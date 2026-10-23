-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_two_zero_stratifications
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.two_zero_stratifications
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:29:04.689598+00:00
-- url     : https://prove2.me/theorems/1de47046-37f1-4c73-910a-2b7baede6f0c
-- title:
--   Remark 59
-- statement:
--   Let $\psi:[0,1]\to\operatorname{Sp}(2n,\mathbb R)$ be continuous, and let $V=\{0\}\times\mathbb R^n$. The two indices have different vanishing strata:
--
--   $$\dim(\psi(t)V\cap V)\equiv k\ (0\le k\le n)\ \Longrightarrow\ \mu_{\rm RS2}(\psi)=0,$$
--   $$\dim\ker(\psi(t)-I)\equiv k\ (0\le k\le2n)\ \Longrightarrow\ \mu_{\rm RS}(\psi)=0.$$
--
--   The vertical intersection is represented by its isomorphic pullback $V\cap\psi(t)^{-1}V$. These are sufficient conditions for zero index, not descriptions of the complete zero sets. Neither assertion restricts the endpoints.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 59, Remark 59

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Remark 59, PDF p.59: two distinct constant-intersection stratifications. -/
theorem two_zero_stratifications {n : ℕ} :
    (∀ p : ℝ → GroupedRealMatrix n, IsPath p 1 → ∀ k : ℕ, k ≤ n →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Module.finrank ℝ (crossingSpace true (p t)) = k) →
        robbinSalamonVertical p = 0) ∧
    (∀ p : ℝ → GroupedRealMatrix n, IsPath p 1 → ∀ k : ℕ, k ≤ 2*n →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Module.finrank ℝ (crossingSpace false (p t)) = k) →
        robbinSalamon p = 0) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
