-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P75_generalizedRecovery_multiplicative
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P75.generalizedRecovery_multiplicative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:47:15.163508+00:00
-- url     : https://prove2.me/theorems/42f329d7-c9f5-49d2-b768-6f883dced6bf
-- title:
--   Generalized fidelity of recovery is multiplicative
-- statement:
--   Let $A,B,C,A',B',C'$ be finite-dimensional nonzero complex quantum systems, and let $\rho_{AB},\tau_{A'B'},\sigma_{AC},\omega_{A'C'}$ be density operators. Define the squared fidelity $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ and generalized recovery fidelity by $F_{C\to B}(\rho\|\sigma)=\sup_\Gamma F(\rho,(\mathrm{id}_A\otimes\Gamma)(\sigma))$, where $\Gamma:C\to B$ ranges over every CPTP map. Then
--
--   $$
--   F_{CC'\to BB'}(\rho_{AB}\otimes\tau_{A'B'}\|\sigma_{AC}\otimes\omega_{A'C'})
--   =F_{C\to B}(\rho_{AB}\|\sigma_{AC})F_{C'\to B'}(\tau_{A'B'}\|\omega_{A'C'}).
--   $$
--
--   The two $A$ marginals may differ, and the two $A'$ marginals may differ. The joint optimization permits arbitrary joint channels. This identity is the paper's main technical multiplicativity result.
-- source:
--   The Fidelity of Recovery is Multiplicative, arXiv:1502.07973v2, PDF p. 4, Proposition 2, (26)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P75

namespace QAlgorithms.Papers.Independent.Intakenext100.P75

open scoped Matrix ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

variable {A B C D Ap Bp Cp R I J K L : Type}

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype Ap] [DecidableEq Ap] [Nonempty Ap]

variable [Fintype Bp] [DecidableEq Bp] [Nonempty Bp]

variable [Fintype Cp] [DecidableEq Cp] [Nonempty Cp]

variable [Fintype R] [DecidableEq R] [Nonempty R]

/-- Proposition 2, PDF p.4, (26): generalized recovery is multiplicative.
The A marginals may differ; the joint optimization allows all joint channels. -/
theorem generalizedRecovery_multiplicative
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty Ap] [Nonempty Bp] [Nonempty Cp]
    (rho : Mat (A × B)) (tau : Mat (Ap × Bp))
    (sigma : Mat (A × C)) (omega : Mat (Ap × Cp))
    (hrho : IsDensityMatrix rho) (htau : IsDensityMatrix tau)
    (hsigma : IsDensityMatrix sigma) (homega : IsDensityMatrix omega) :
    generalizedRecoveryFidelity (bipartiteTensor rho tau) (bipartiteTensor sigma omega) =
      generalizedRecoveryFidelity rho sigma * generalizedRecoveryFidelity tau omega := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P75
