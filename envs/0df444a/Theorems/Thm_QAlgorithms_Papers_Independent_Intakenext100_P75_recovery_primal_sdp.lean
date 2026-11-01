-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P75_recovery_primal_sdp
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P75.recovery_primal_sdp
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:48:58.362648+00:00
-- url     : https://prove2.me/theorems/7f15e2c7-d18d-47d2-bb79-943d50a0fdf6
-- title:
--   Choi and root-fidelity primal semidefinite programs
-- statement:
--   Let $\rho_{AB}$ and $\sigma_{AC}$ be density operators on finite-dimensional nonzero complex systems, and let $\sigma_{ACD}$ purify $\sigma_{AC}$. Set $s=\sqrt{\sigma_{AD}}\otimes I_B$, reindexed onto $ABD$, and $T(\tau)=\operatorname{tr}_D(s\tau s)$. Then both following maxima are attained:
--
--   $$
--   F_{C\to B}(\rho\|\sigma)=\max_{\substack{\tau_{ABD}\ge0\\\operatorname{tr}_B\tau=I_{AD}}}F(\rho_{AB},T(\tau)),
--   $$
--
--   $$
--   \sqrt{F_{C\to B}(\rho\|\sigma)}
--   =\max_{\substack{\tau\ge0,\ \operatorname{tr}_B\tau=I_{AD}\\Z\in\mathcal L(AB),\ \left(\begin{smallmatrix}\rho&Z\\Z^\dagger&T(\tau)\end{smallmatrix}\right)\ge0}}
--   \frac12\operatorname{tr}(Z+Z^\dagger).
--   $$
--
--   Here $F$ is squared Uhlmann fidelity. The Choi variable $\tau$ is positive but unnormalized; the second program optimizes root fidelity. These are the primal optimization formulations used in the duality argument, including for singular purifications.
-- source:
--   The Fidelity of Recovery is Multiplicative, arXiv:1502.07973v2, PDF p. 3, Section II, (15),(16)

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

/-- PDF p.3, (15),(16): both primal maxima are attained; (16) optimizes
ROOT fidelity, whereas (15) optimizes squared fidelity. -/
theorem recovery_primal_sdp
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] (rho : Mat (A × B)) (sigma : Mat (A × C))
    (purification : Mat ((A × C) × D))
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hpure : IsPure purification) (hmarginal : traceRight purification = sigma) :
    IsGreatest {v : ℝ | ∃ t : Mat ((A × B) × D), t.PosSemidef ∧
      (Matrix.of fun x y : A × D => ∑ b, t ((x.1, b), x.2) ((y.1, b), y.2)) = 1 ∧
      v = fidelity rho (choiOutput (marginalAD purification) t)} (generalizedRecoveryFidelity rho sigma) ∧
    IsGreatest {v : ℝ | ∃ t : Mat ((A × B) × D), ∃ z : Mat (A × B),
      t.PosSemidef ∧
      (Matrix.of fun x y : A × D => ∑ b, t ((x.1, b), x.2) ((y.1, b), y.2)) = 1 ∧
      (Matrix.fromBlocks rho z z.conjTranspose
        (choiOutput (marginalAD purification) t)).PosSemidef ∧
      v = (z + z.conjTranspose).trace.re / 2} (Real.sqrt (generalizedRecoveryFidelity rho sigma)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P75
