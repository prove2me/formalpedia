-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_negativity_notMonotone
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.negativity_notMonotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:37:15.460848+00:00
-- url     : https://prove2.me/theorems/6d9e58f4-0041-4233-8de6-65bf779c8e14
-- title:
--   Theorem 10: negativity fails to be PPT-preserving monotone
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. There exist an integer $d>3$, a density matrix $\rho$ on $d\times d$, and a PPT-preserving channel $\Lambda$ on that register, for which
--
--   $$\mathcal N(\Lambda(\rho))>\mathcal N(\rho),\qquad \mathcal N(\rho)=\frac{\|\rho^\Gamma\|_1-1}{2}.$$
--
--   Here $\Gamma$ is first-party partial transpose. PPT-preserving means preserving the whole PPT positive cone.
--
--   This is an existential failure of monotonicity.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 13, Theorem 10

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

/-- Theorem 10, PDF pp.13-14: existential failure of negativity monotonicity
under PPT preservation, rather than under the PPT-Choi condition. -/
theorem negativity_notMonotone :
    ∃ d : ℕ, 3 < d ∧ ∃ rho : Bip d d,
      ∃ L : Superop (Fin d × Fin d) (Fin d × Fin d),
        IsDensityMatrix rho ∧ IsChannel L ∧ PPTPreserving L ∧
        negativity rho < negativity (L rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
