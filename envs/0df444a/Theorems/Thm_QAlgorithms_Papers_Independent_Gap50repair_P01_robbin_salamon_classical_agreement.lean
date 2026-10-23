-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_robbin_salamon_classical_agreement
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.robbin_salamon_classical_agreement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:26:29.041261+00:00
-- url     : https://prove2.me/theorems/ef484b16-3c22-4ae9-8813-989bb15772ff
-- title:
--   Proposition 52
-- statement:
--   Let $n\ge1$ and let $\psi:[0,1]\to\operatorname{Sp}(2n,\mathbb R)$ be continuous with $\psi(0)=I$ and $\det(\psi(1)-I)\ne0$. Then $\mu_{\rm RS}(\psi)=\mu_{\rm CZ}(\psi)$. If in addition $\psi$ is smooth and all its crossings are regular, put $S_0=-J_0\dot\psi_0$. Then
--
--   $$\mu_{\rm CZ}(\psi)=\tfrac12\operatorname{Sign}S_0+\sum_{0<t<1\atop t\ \rm crossing}\operatorname{Sign}\Gamma(\psi,t).$$
--
--   The initial kernel is the full space and the final kernel is zero. This includes both the equality of the two definitions and its crossing-form consequence.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 50, Proposition 52

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 52, PDF pp.50–51: agreement and the in-particular formula. -/
theorem robbin_salamon_classical_agreement {n : ℕ} (hn : 1 ≤ n)
    (p : ℝ → GroupedRealMatrix n) (hp : IsAdmissible p 1) :
    robbinSalamon p = (conleyZehnder p 1 : ℚ) ∧
    (IsRegular false p → (conleyZehnder p 1 : ℚ) =
      (matrixSignature (-jMatrix n*pathDerivative p 0) : ℚ)/2 +
        (interiorCrossingSum false p : ℚ)) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
