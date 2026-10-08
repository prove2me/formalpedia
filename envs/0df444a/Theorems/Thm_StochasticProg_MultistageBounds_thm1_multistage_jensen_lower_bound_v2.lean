-- Prove2me | Theorems.Thm_StochasticProg_MultistageBounds_thm1_multistage_jensen_lower_bound_v2
-- name    : StochasticProg.MultistageBounds.thm1_multistage_jensen_lower_bound_v2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:57:36.463991+00:00
-- url     : https://prove2.me/theorems/f8c0d690-34c2-43b5-bb9a-230fec362766
-- title:
--   Chapter 10, Theorem 1 — multistage Jensen lower bound via aggregation (corrected)
-- statement:
--   Corrected version (v2) of Chapter 10, Theorem 1 (p. 419) of Birge & Louveaux, *Introduction to Stochastic Programming*: the aggregated multistage problem (1.2) gives a lower bound on the exact multistage problem (1.1).
--
--   Let `TFine` and `TCoarse` be scenario trees with $H$ stages, with instances on each, and let `agg` send every exact node to its aggregated block, preserving the root, the stages and the ancestor map. Suppose the deterministic data agree ($W$ and $c$, p. 418), the aggregated right-hand sides and technology matrices are the probability-weighted conditional expectations of the exact ones over each block, and — the book's condition that these expectations be "independent of the past" (p. 419) — for every exact node $j$ and every aggregated block $i$ following `agg j`, the probability-weighted data of the children of $j$ that fall in $i$ equal $P(i\mid \mathrm{agg}\,j)$ times the block's aggregated data. Then the optimal value of the aggregated problem is at most that of the exact problem.
--
--   This replaces `StochasticProg.MultistageBounds.thm1_multistage_jensen_lower_bound`, which encoded the book's literal "common outcome" clause instead; that clause is too weak, and the recorded disproof is a counterexample to it.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, Ch. 10 Theorem 1, printed p. 419 ("independent of the past", p. 419; deterministic W and c, p. 418)

import Mathlib
import Definitions.Def_StochasticProg_MultistageBounds_Tree
import Definitions.Def_StochasticProg_MultistageBounds_Instance

namespace StochasticProg.MultistageBounds

open scoped Matrix

variable {H n m : ℕ}

/-- Chapter 10, Theorem 1 (Birge & Louveaux, p. 419): the aggregated multistage problem (1.2)
provides a lower bound on the exact multistage problem (1.1), provided the aggregated data are
conditional expectations of the exact data (`hCoarse_h`/`hCoarse_T`) and these expectations are
"independent of the past" (the sentence just before the theorem, p. 419), stated at the fine-node level as
`hIndepPast`: for every exact node `j` and every aggregated block `i` following `agg j`, the probability-weighted
data of the children of `j` that fall in `i` equal `P(i | agg j)` times the block's aggregated data. `agg` sends
every exact node to its aggregated node, preserving the root, stages and ancestors.

v2 (2026-10-05): the published statement was disproved. It used the book's literal "common outcome" clause
(`hCommonOutcome`), which is too weak: the recorded disproof is also a counterexample to that wording. This
version replaces it with the independence-of-the-past condition the book's proof uses (`hIndepPast`). -/
theorem thm1_multistage_jensen_lower_bound_v2
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
    -- p. 419: "(h̄ᵗᵢ, T̄ᵗᵢ) … independent of the past": for every fine history node j and every
    -- aggregated block i following agg j, E[1{Sᵢ}·(h,T) | j] = P(i | agg j)·(h̄ᵢ, T̄ᵢ)
    (hIndepPast : ∀ (j : TFine.Node) (i : TCoarse.Node), i ∈ TCoarse.children (agg j) →
      (∑ k ∈ (TFine.children j).filter (fun k => agg k = i), fine.p k • fine.h k =
          (fine.p j * coarse.p i / coarse.p (agg j)) • coarse.h i) ∧
      (∑ k ∈ (TFine.children j).filter (fun k => agg k = i), fine.p k • fine.Tmat k =
          (fine.p j * coarse.p i / coarse.p (agg j)) • coarse.Tmat i))
    (zFine zCoarse : ℝ)
    (hzFine_lb : ∀ x, Feasible fine x → zFine ≤ obj fine x)
    (hzFine_attain : ∃ x, Feasible fine x ∧ obj fine x = zFine)
    (hzCoarse_lb : ∀ x, Feasible coarse x → zCoarse ≤ obj coarse x)
    (hzCoarse_attain : ∃ x, Feasible coarse x ∧ obj coarse x = zCoarse) :
    zCoarse ≤ zFine := by
  sorry

end StochasticProg.MultistageBounds
