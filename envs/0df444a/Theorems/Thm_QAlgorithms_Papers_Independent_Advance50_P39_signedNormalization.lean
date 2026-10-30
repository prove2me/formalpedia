-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P39_signedNormalization
-- name    : QAlgorithms.Papers.Independent.Advance50.P39.signedNormalization
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:03:07.657994+00:00
-- url     : https://prove2.me/theorems/42a067d9-ad93-47b0-bc5e-9eef634a85c2
-- title:
--   Separate normalization of nonempty positive and negative sign classes
-- statement:
--   Let $(\eta_k)_{k=1}^r$ be a finite family of real contributions. Define $P=\{k:\eta_k>0\}$, $N=\{k:\eta_k<0\}$, $\eta^+=\sum_{k\in P}\eta_k$ and $\eta^-=\sum_{k\in N}\eta_k$. Then $\sum_k\eta_k=\eta^++\eta^-$. Each nonempty sign class has a nonzero total of its indicated sign and normalizes separately:
--   $$
--   \sum_{k\in P}\frac{\eta_k}{\eta^+}=1\quad(P\ne\varnothing),\qquad
--   \sum_{k\in N}\frac{\eta_k}{\eta^-}=1\quad(N\ne\varnothing).
--   $$
--   Each ratio in its sign class lies in $(0,1]$. In particular the negative-class ratios are positive magnitudes, and an empty class has no percentage interpretation. This is a conditional algebraic normalization of finite real inputs; it does not assert that the source's infinite-time Eq. (11) supplies finite values.
-- source:
--   Role of quantum coherence in chromophoric energy transport, arXiv:0806.4725v2, PDF p. 5, §V, Eq.(12): normalization within each nonempty sign class

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich semigroupEvolution)

namespace QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.5--6, Eq. (12): each nonempty sign class separately normalizes to one.
Negative-class ratios are positive magnitudes. This is conditional finite-real
algebra, independent of the convergence problem with the source's Eq. (11). -/
theorem signedNormalization {r : ℕ} (eta : Fin r → ℝ) :
    (∑ k, eta k) = (∑ k ∈ positiveIndices eta, eta k) +
      (∑ k ∈ negativeIndices eta, eta k) ∧
    ((positiveIndices eta).Nonempty →
      0 < (∑ k ∈ positiveIndices eta, eta k) ∧
      (∑ k ∈ positiveIndices eta, normalizedContribution eta (positiveIndices eta) k) = 1 ∧
      ∀ k ∈ positiveIndices eta, 0 < normalizedContribution eta (positiveIndices eta) k ∧
        normalizedContribution eta (positiveIndices eta) k ≤ 1) ∧
    ((negativeIndices eta).Nonempty →
      (∑ k ∈ negativeIndices eta, eta k) < 0 ∧
      (∑ k ∈ negativeIndices eta, normalizedContribution eta (negativeIndices eta) k) = 1 ∧
      ∀ k ∈ negativeIndices eta, 0 < normalizedContribution eta (negativeIndices eta) k ∧
        normalizedContribution eta (negativeIndices eta) k ≤ 1) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P39

end
