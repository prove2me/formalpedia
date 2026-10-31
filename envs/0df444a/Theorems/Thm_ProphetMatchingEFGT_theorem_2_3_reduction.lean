-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_theorem_2_3_reduction
-- name    : ProphetMatchingEFGT.theorem_2_3_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:50:48.557985+00:00
-- url     : https://prove2.me/theorems/49c3d1b0-a44e-4f30-80db-f15ec7ff5a74
-- title:
--   Theorem 2.3 — a $c$-batched OCRS for $R(w,F)$ yields a $c$-competitive batched prophet algorithm
-- statement:
--   Let $E$ be finite, $\mathcal M$ a downward closed family of feasible sets, and $\mathcal B$ any set of ordered partitions of $E$. Let $w\sim\mu$ have integrable coordinates, with independent batch blocks for every partition in $\mathcal B$, and let $\mathrm{OPT}$ be a deterministic maximum-weight feasible set with measurable level sets. Suppose a measurable batched OCRS is $c$-selectable for the sampling scheme $R(w,F)$ on every partition of $\mathcal B$. Then there is a single measurable batched prophet algorithm, which does not know in advance which partition of $\mathcal B$ (and which arrival order) it faces, such that for every $(B_t)_t\in\mathcal B$
--   $$\mathbb E_{w,I}[w(I)]\ \ge\ c\cdot\mathbb E_w\big[w(\mathrm{OPT}(w))\big].$$
--
--   This is the reduction from prophet inequalities to online contention resolution that the paper applies to vertex and edge arrivals.
--
--   Differences from the source:
--   - encoding: w ∼ F = ∏_t F_t (independence across batches, dependence within) → one law μ on E → ℝ under which the batch blocks of the partition are mutually independent (iIndepFun); reason: same instances
--   - encoding: OPT a deterministic function returning a maximum-weight feasible set (p.8, footnote 5) → any opt with opt w ∈ M, maximal weight, and measurable level sets {w | opt w = S}; reason: measurability is needed for Pr[OPT(w) = S] to be defined; the theorem holds for every such OPT
--   - encoding: finite expectations, presupposed by the ratio → Integrable coordinates / weights; reason: without it the Bochner integrals are 0 (slip 8)
--   - encoding: Pr[e ∈ I_t | R_t = S] ≥ c (Definition 2.1, eq. (1)) → product form Pr[A, B] ≥ c·Pr[B] (or the corresponding product of probabilities); reason: the conditional probability is undefined on null events (slip 6); equal where it is defined
--   - reading: a c-batched OCRS for the sampling scheme R(w, F) → a c-selectable OCRS on every partition in 𝓑, with R_t independent and distributed as OPT(w) ∩ B_t (properties 1 and 3 of §2.3); reason: the scheme's law depends on the partition the adversary picks
--   - encoding: online algorithms (Definitions 2.1, 2.2) → rules with history, internal randomness and measurable decisions; the run discards a choice that is not a feasible subset of the allowed set; reason: a rule that proposes feasible subsets runs unchanged; measurability makes the probabilities those of events
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, Theorem 2.3, p. 8 (with Definitions 2.1–2.2, p. 7–8)

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_BatchedModel

open MeasureTheory ProbabilityTheory

namespace ProphetMatchingEFGT

/-- **Theorem 2.3 (reduction from c-batched prophet inequality to c-batched OCRS), p. 8.**
Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, Theorem 2.3, p. 8: "For every set `B` of feasible
ordered partitions, given a c-batched OCRS for the sampling scheme `R(w, F)` with `w ∼ F`, there is
a batched prophet inequality algorithm for `w ∼ F` with competitive ratio c."

**Formalization Note.** `𝓑` is any set of ordered partitions of `E`; under `μ` the batches of each
of them are independent (§2.2, p. 7, and footnote 3). `opt` is any deterministic optimum with
measurable level sets (footnote 5). Selectability is the product form of eq. (1). The prophet
algorithm is one rule for all partitions in `𝓑` (it does not know the partition in advance) and is
measurable. -/
theorem theorem_2_3_reduction {E : Type*} [Fintype E] [DecidableEq E] (M : Set (Finset E))
    (hM : IsDownwardClosed M) (𝓑 : Set (List (Finset E)))
    (h𝓑 : ∀ Bs ∈ 𝓑, IsOrderedPartition Bs) (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ e, Integrable (fun w => w e) μ) (hind : ∀ Bs ∈ 𝓑, BlocksIndep μ Bs)
    (opt : (E → ℝ) → Finset E) (hopt : IsOPT M opt) (c : ℝ) (A : BatchedRule E (Finset E))
    (hA : A.MeasurableOCRS) (hsel : IsSelectableBatchedOCRS A M μ opt 𝓑 c) :
    ∃ P : BatchedRule E (E → ℝ), P.MeasurableProphet ∧
      ∀ Bs ∈ 𝓑, c * optBenchmark μ opt ≤ prophetValue P M μ Bs := by sorry

end ProphetMatchingEFGT
