-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_negativity_unboundedRatio
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.negativity_unboundedRatio
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:49:07.889302+00:00
-- url     : https://prove2.me/theorems/03184e86-f1d9-4f30-9ce1-d2eb7e651303
-- title:
--   Exact and unbounded negativity ratio
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. For every integer $d>3$, let $F_d$ be the swap, $\rho=(I-F_d)/(d(d-1))$, $A=(dI+F_d)/(d+1)$, and $\Lambda(X)=\operatorname{Tr}(AX)I_{d^2}/d^2+\operatorname{Tr}((I-A)X)\phi_d^+$. Then $\rho$ is a state, $\Lambda$ is a PPT-preserving channel, and
--
--   $$\mathcal N(\rho)=\frac1d,\qquad\mathcal N(\Lambda(\rho))=\frac{d-1}{2d},\qquad\frac{\mathcal N(\Lambda(\rho))}{\mathcal N(\rho)}=\frac{d-1}{2}.$$
--
--   Consequently, for every real $C>0$, some $d>3$ in this family has $0<\mathcal N(\rho)$ and $\mathcal N(\Lambda(\rho))>C\mathcal N(\rho)$.
--
--   The dimension varies to produce arbitrary multiplicative increase.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 14, unbounded-negativity-ratio

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- PDF p.14: the exact ratio for the source's constructed state/channel,
and its consequence of an unbounded multiplicative increase as dimension varies. -/
theorem negativity_unboundedRatio :
    (∀ d : ℕ, 3 < d → IsDensityMatrix (antisymmetricDensity d) ∧
      IsChannel (negativityMap d) ∧ PPTPreserving (negativityMap d) ∧
      negativity (antisymmetricDensity d) = 1 / (d : ℝ) ∧
      negativity (negativityMap d (antisymmetricDensity d)) = ((d : ℝ) - 1) / (2 * d) ∧
      negativity (negativityMap d (antisymmetricDensity d)) / negativity (antisymmetricDensity d) =
        ((d : ℝ) - 1) / 2) ∧
    (∀ C : ℝ, 0 < C → ∃ d : ℕ, 3 < d ∧
      0 < negativity (antisymmetricDensity d) ∧
      C * negativity (antisymmetricDensity d) < negativity (negativityMap d (antisymmetricDensity d))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
