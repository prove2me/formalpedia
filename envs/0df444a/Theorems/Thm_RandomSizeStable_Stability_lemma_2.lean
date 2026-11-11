-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_lemma_2
-- name    : RandomSizeStable.Stability.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:59.076813+00:00
-- url     : https://prove2.me/theorems/0a6ed756-e8a1-4053-b88e-23e00ada01bc
-- title:
--   Lemma 2 — mean-zero marked score and optimum-position bound
-- statement:
--   Let $D$ be a positive-integer draw law and $P$ a random-size stable lottery on a finite nonempty strict-ranking profile. Arrange its candidate blocks worst to best for each voter $v$. For any subset $H$ of candidates write $H_v$ for their union. For any designated candidate $o$ let $r_v$ be the mass strictly below $o$. Then
--   $$\mathbb E_v\left[\int_{H_v}(\phi_D(u)-\mu_D)\,du\right]=0,
--   \qquad \mathbb E_v[\phi_D(r_v)]\le\mu_D.$$
--   Here the voter is uniform. The designated candidate need not be optimal and may have zero lottery mass.
--
--   These are the two stability consequences used by the rank-cut distortion criterion.
--
--   Differences from the source:
--   - encoding: finite nonempty voter and candidate sets with strict rankings → finite nonempty types and Election strict total orders; reason: these represent exactly the finite profiles in Section 2, with uniform voter averaging
--   - encoding: a positive-integer-valued random variable D → a PMF on the positive integers; reason: only the law enters these claims; countably infinite support and infinite mean remain allowed
--   - encoding: rank blocks with immaterial endpoint choices → half-open blocks and their union; reason: Lebesgue integrals ignore the finitely many block endpoints
-- source:
--   Nisarg Shah, Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission #1342 (October 2026), p. 12, Lemma 2.

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankBlocks

set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion

namespace RandomSizeStable.Stability

/-- Lemma 2, p.12: arbitrary marked subsets and arbitrary designated candidates. -/
theorem lemma_2 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
    (D : PMF ℕ+) (E : Election V C) (P : C → ℝ) (hP : IsStable D E P) :
    (∀ H : Set C, voterMean (fun v =>
      ∫ u in markedRegion E P v H, (pgf D u - benchmark D)) = 0) ∧
    (∀ o : C, voterMean (fun v => pgf D (leftRank E P v o)) ≤ benchmark D) := by sorry

end RandomSizeStable.Stability
