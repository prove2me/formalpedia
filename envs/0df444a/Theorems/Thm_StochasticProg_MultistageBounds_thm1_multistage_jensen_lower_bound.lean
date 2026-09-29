-- Prove2me | Theorems.Thm_StochasticProg_MultistageBounds_thm1_multistage_jensen_lower_bound
-- name    : StochasticProg.MultistageBounds.thm1_multistage_jensen_lower_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:16:22.491536+00:00
-- url     : https://prove2.me/theorems/bed38aa5-9bcc-48fd-8d6f-459548f2c78f
-- title:
--   Chapter 10, Theorem 1 — multistage Jensen lower bound via aggregation
-- statement:
--   **Chapter 10, Theorem 1** (Birge & Louveaux, p. 419): the multistage generalization of
--   Chapter 8's two-period Jensen lower bound — the optimal value of the *aggregated* multistage
--   problem (1.2) never exceeds the optimal value of the *exact* multistage problem (1.1),
--   provided the aggregation is built from genuine conditional expectations of the exact data
--   **and** every two aggregated nodes that "have a common outcome at time `t`" are assigned the
--   *same* aggregated data.
--
--   Fix a stage count `H`, dimensions `n, m`, an exact scenario tree `TFine : Tree H` and a
--   coarser, aggregated scenario tree `TCoarse : Tree H` (in the sense of the companion `Tree`
--   definition), and instances `fine : Instance H n m TFine`, `coarse : Instance H n m TCoarse`.
--   Let `agg : TFine.Node → TCoarse.Node` send every exact node to the aggregated node of its
--   block `Sᵗᵢ`, respecting the tree structure: `agg` sends the exact root to the aggregated
--   root, preserves `stage`, and commutes with the ancestor map. Suppose the shared,
--   deterministic data agree — `fine.W = coarse.W` and `fine.c j = coarse.c (agg j)` for every
--   exact node `j` (Birge & Louveaux's "`cᵗ = cᵗ`" and "`Wᵗ` known and not random", p. 418) —
--   and that the aggregated technology/right-hand-side data are the genuine
--   probability-weighted conditional expectations of the exact data over each aggregation fiber,
--   $$
--   p^{\mathrm{coarse}}_i\, h^{\mathrm{coarse}}_i = \sum_{j : \mathrm{agg}(j) = i} p^{\mathrm{fine}}_j\, h^{\mathrm{fine}}_j, \qquad
--   p^{\mathrm{coarse}}_i\, T^{\mathrm{coarse}}_i = \sum_{j : \mathrm{agg}(j) = i} p^{\mathrm{fine}}_j\, T^{\mathrm{fine}}_j
--   \quad (\mathrm{stage}(i) \ne 0),
--   $$
--   i.e. $(\bar h^t_i, \bar T^t_i) = \mathbb E^{S^t_i}[(h^t,T^t)]$, exactly Birge & Louveaux's
--   definitions preceding the theorem (p. 418). Finally — the theorem's own extra hypothesis,
--   stated with a label type `Θ` and `curOutcome : TCoarse.Node → Θ` recording each aggregated
--   node's current-period outcome — suppose that whenever two aggregated nodes `i, i'` at the
--   same stage share a current-period outcome (`curOutcome i = curOutcome i'`), their aggregated
--   data already coincide: `coarse.h i = coarse.h i'` and `coarse.Tmat i = coarse.Tmat i'`. This
--   is the book's "`E^{S^t_i}[(h^t,T^t)] = (\bar h^t_i,\bar T^t_i) = E^{S^t_j}[(h^t,T^t)]` for all
--   `S^t_i` and `S^t_j` that have a common outcome at time `t`."
--
--   Then, for `zFine`/`zCoarse` the optimal values of (1.1)/(1.2) (each characterized as a lower
--   bound over the feasible tree-wide decisions, attained at some feasible point),
--   $$
--   z^{\mathrm{coarse}} \;\le\; z^{\mathrm{fine}} .
--   $$
--
--   **Formalization Note** The book's own printed statement of the hypothesis has a shift: "such
--   that `(ωt−1,ωt) ∈ Stj` if and only if there exist some `(ω̂t−1,ωt) ∈ Stj`" repeats `S^t_j` on
--   both sides of the "if and only if" where the sentence's own subject ("`S^t_i` and `S^t_j`
--   that have a common outcome") requires the left side to range over `S^t_i` — confirmed as the
--   book's own printed text (not an artefact of text extraction) by rendering PDF page 436
--   directly; see `STATUS.md`. This formalization reads the corrected clause as: `S^t_i` and
--   `S^t_j` project onto the same set of period-`t` outcomes, abstracted here to an arbitrary
--   label type `Θ` (`curOutcome`) rather than a literal projection onto a product-space
--   coordinate, since the aggregated tree alone (without also formalizing the exact per-period
--   outcome spaces `Ω_t` as a product) does not otherwise have a "period-`t` outcome" object to
--   project onto. `zFine`/`zCoarse` are hypothesis-characterized (a lower bound over the feasible
--   set, attained), not `sInf`-defined, to avoid the real infimum's junk value `0` on an
--   unbounded-below or empty feasible set (`reference/FAITHFULNESS_TRAPS.md` trap 5) — neither
--   problem's constraints are shown bounded or nonempty a priori by the hypotheses above.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 419, Chapter 10, Theorem 1

import Mathlib
import Definitions.Def_StochasticProg_MultistageBounds_Tree
import Definitions.Def_StochasticProg_MultistageBounds_Instance

namespace StochasticProg.MultistageBounds

open scoped Matrix

variable {H n m : ℕ}

/-- Chapter 10, Theorem 1 (Birge & Louveaux, p. 419): the aggregated multistage problem (1.2)
provides a lower bound on the exact multistage problem (1.1), provided the aggregated data are
genuinely conditional expectations of the exact data (`hCoarse_h`/`hCoarse_T`) *and* two
aggregated nodes that share a common current-period outcome receive the same aggregated data
(`hCommonOutcome`, the theorem's own extra hypothesis: "`E^{Sti}[(ht,Tt)] = (h̄ti,T̄ti) =
E^{Stj}[(ht,Tt)]` for all `Sti` and `Stj` that have a common outcome at time `t`"). Without
`hCommonOutcome`, (1.2)'s conditional-expectation form need not actually be a bound (p. 419,
two paragraphs before the theorem statement: "If not, then the conditional expectation form in
(1.2) may not actually achieve a bound"). `agg` sends every exact node to the aggregated node
of its `St_i`; `curOutcome` labels each aggregated node by the current-period outcome its `St_i`
shares with any node it has "a common outcome at time `t`" with — this is a deliberate
generalization of the book's literal `(ωt−1,ωt) ∈ Sti ⟺ ∃ω̂t−1,(ω̂t−1,ωt) ∈ Stj` clause (the PDF's
own printed text repeats `Stj` on both sides of that "if and only if", a genuine typo in the
book, confirmed against a fresh render of the page rather than assumed from OCR — see
`STATUS.md`; the natural reading replaces the first `Stj` with `Sti`, i.e. `Sti` and `Stj`
project to the same set of period-`t` outcomes), abstracted to an arbitrary label type `Θ`
rather than a literal product-space projection. -/
theorem thm1_multistage_jensen_lower_bound
    (TFine TCoarse : Tree H)
    (fine : Instance H n m TFine) (coarse : Instance H n m TCoarse)
    (agg : TFine.Node → TCoarse.Node)
    (hagg_root : agg TFine.root = TCoarse.root)
    (hagg_stage : ∀ j : TFine.Node, TCoarse.stage (agg j) = TFine.stage j)
    (hagg_anc : ∀ j : TFine.Node, (TFine.stage j).val ≠ 0 →
      agg (TFine.anc j) = TCoarse.anc (agg j))
    (hW_agree : fine.W = coarse.W)
    (hc_agree : ∀ j : TFine.Node, fine.c j = coarse.c (agg j))
    (hCoarse_h : ∀ i : TCoarse.Node,
      coarse.p i • coarse.h i =
        ∑ j ∈ Finset.univ.filter (fun j : TFine.Node => agg j = i), fine.p j • fine.h j)
    (hCoarse_T : ∀ i : TCoarse.Node, (TCoarse.stage i).val ≠ 0 →
      coarse.p i • coarse.Tmat i =
        ∑ j ∈ Finset.univ.filter (fun j : TFine.Node => agg j = i), fine.p j • fine.Tmat j)
    (Θ : Type) (curOutcome : TCoarse.Node → Θ)
    (hCommonOutcome : ∀ i i' : TCoarse.Node, TCoarse.stage i = TCoarse.stage i' →
      curOutcome i = curOutcome i' → coarse.h i = coarse.h i' ∧ coarse.Tmat i = coarse.Tmat i')
    (zFine zCoarse : ℝ)
    (hzFine_lb : ∀ x, Feasible fine x → zFine ≤ obj fine x)
    (hzFine_attain : ∃ x, Feasible fine x ∧ obj fine x = zFine)
    (hzCoarse_lb : ∀ x, Feasible coarse x → zCoarse ≤ obj coarse x)
    (hzCoarse_attain : ∃ x, Feasible coarse x ∧ obj coarse x = zCoarse) :
    zCoarse ≤ zFine := by sorry

end StochasticProg.MultistageBounds
