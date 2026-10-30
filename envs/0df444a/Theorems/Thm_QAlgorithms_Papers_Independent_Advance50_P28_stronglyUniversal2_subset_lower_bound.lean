-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_stronglyUniversal2_subset_lower_bound
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.stronglyUniversal2_subset_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:45:42.779282+00:00
-- url     : https://prove2.me/theorems/02e3aeb6-6874-4f5b-b266-986664bbeb81
-- title:
--   Theorem 2 (19)
-- statement:
--   All logarithms are natural and $d_1$ is the full $L^1$ distance. Let $P$ be a normalized law on a finite nonempty alphabet $A$, and let $U_M$ be the uniform law on $M\ge1$ symbols. For a map $f$, write $f_*P$ for its pushforward. A strongly universal ensemble here means that every $f_X(a)$ is uniform and independent of the entire tuple $(f_X(a'))_{a'\ne a}$. For every $\Omega\subseteq A$ with $|\Omega|<M$,
--   $$\mathbb E_Xd_1(f_{X*}P,U_M)\ge\left(1-\frac{|\Omega|}{M}\right)^2P(\Omega).$$
--   This is a lower bound on the ensemble average, including the empty-subset case.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 5, Theorem 2 (19)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.5, Theorem 2, (19); normalized law as used in Appendix A, p.17. -/
theorem stronglyUniversal2_subset_lower_bound {A : Type*} [Fintype A] [Nonempty A]
    {M : ℕ} (hM : 0 < M) (h : HashEnsemble A M) (hu : StronglyUniversal2 h)
    (P : A → ℝ) (hP : IsLaw P) (omega : Finset A) (hsize : omega.card < M) :
    (1 - (omega.card : ℝ) / (M : ℝ)) ^ 2 * (∑ a ∈ omega, P a) ≤
      expectedError h P := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
