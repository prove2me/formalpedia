-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P90_matrix_irreversibility_criterion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P90.matrix_irreversibility_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:27:12.017284+00:00
-- url     : https://prove2.me/theorems/8be795d2-1429-4e38-8782-4fed0696e0f9
-- title:
--   A corrected explicit matrix witness for irreversibility
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with fixed orthonormal product bases and positive local dimensions. A state is a positive semidefinite operator of trace one. All logarithms are base two and all operational rates are measured in standard Bell pairs (ebits) per input copy, with deterministic operations and error tending to zero. Write $E_D,E_C$ for distillable entanglement and entanglement cost under completely PPT-preserving CPTP operations; an explicit LOCC subscript denotes unrestricted two-way local operations and classical communication.
--
--   Let $\rho$ be a bipartite state and $P$ its support projection. Suppose a Hermitian matrix $Y$ satisfies $Y-P^{T_B}\ge0$, $Y+P^{T_B}\ge0$, and $\|Y^{T_B}\|_\infty>0$. If
--
--   $$\|\rho^{T_B}\|_1<\|Y^{T_B}\|_\infty^{-1},$$
--
--   then
--
--   $$E_D(\rho)<E_C(\rho).$$
--
--   **Source correction.** The printed pair is $P^{T_B}\pm Y\ge0$; it is corrected to $Y\pm P^{T_B}\ge0$, in agreement with Eqs. (4), (12) and the constructed witness on p. 5. The printed pair forces $P^{T_B}\ge0$. The norm guard is automatic for a feasible normalized-state support and excludes inverse-at-zero defaults.
-- source:
--   Irreversibility of Asymptotic Entanglement Manipulation Under Quantum Operations Completely Preserving Positivity of Partial Transpose, arXiv:1606.09421v3, PDF p. 4, Unnumbered explicit matrix witness sufficient condition, with recorded source sign correction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P90

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P90

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P36
  (relativeEntropy rains target canonicalMatrix allowed pptDistillable)

open QAlgorithms.Papers.Independent.Information100.P04 (gamma copies IsPPT)

open QAlgorithms.Papers.Independent.Next46.P42 (regroupProduct)

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Gap48.P32 (antisymmetricQutrit)

/-- arXiv:1606.09421v3, PDF p.4: corrected matrix-witness criterion.
PRINTED: P^TB plus or minus Y >= 0. CHANGED: Y plus or minus P^TB >= 0. WHY: Eqs.(4),(12)
and the p.5 witness require -Y<=P^TB<=Y; the printed pair instead forces
P^TB>=0. Independent moderation must confirm this recorded source correction.
The positive norm guard is automatic for a feasible normalized-state support. -/
theorem matrix_irreversibility_criterion {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho Y : Matrix (A × B) (A × B) ℂ) (hstate : IsDensityMatrix rho)
    (hY : etaFeasible rho Y) (hnorm : 0 < specNorm (gamma Y))
    (hgap : traceNorm (gamma rho) < (specNorm (gamma Y))⁻¹) :
    pptDistillable rho < asymptoticEntanglementCost false rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P90

end
