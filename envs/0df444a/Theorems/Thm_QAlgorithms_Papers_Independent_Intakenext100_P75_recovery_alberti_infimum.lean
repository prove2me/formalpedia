-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P75_recovery_alberti_infimum
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P75.recovery_alberti_infimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:48:04.661085+00:00
-- url     : https://prove2.me/theorems/bdacc5f5-c9fa-475d-bf82-e8fa38ae674c
-- title:
--   Alberti variational infimum for generalized recovery fidelity
-- statement:
--   Let $\rho_{AB}$ and $\sigma_{AC}$ be density operators on finite-dimensional nonzero complex systems, and let $\sigma_{ACD}$ be any pure-state purification of $\sigma_{AC}$. Write $\sigma_{AD}=\operatorname{tr}_C\sigma_{ACD}$. With squared Uhlmann fidelity and optimization over every local CPTP recovery map, one has
--
--   $$
--   F_{C\to B}(\rho_{AB}\|\sigma_{AC})
--   =\inf_{\substack{R_{AB}>0,\ Q_{AD}>0\\Q_{AD}\otimes I_B\,\ge\,R_{AB}\otimes I_D}}
--   \operatorname{tr}(\rho_{AB}R_{AB}^{-1})\,\operatorname{tr}(\sigma_{AD}Q_{AD}).
--   $$
--
--   The tensor factors in the operator inequality are canonically reordered onto $ABD$. This variational value is useful for multiplicativity. No invertibility of the density operators or full Schmidt rank is assumed.
--
--   **Formalization Note** The printed minimum is corrected to an infimum: orthogonal pure states give zero value without any strictly positive feasible pair attaining zero. Lean states the greatest-lower-bound property.
-- source:
--   The Fidelity of Recovery is Multiplicative, arXiv:1502.07973v2, PDF p. 2, Lemma 1, (10),(25)

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

/-- Lemma 1, PDF pp.2–4, (10),(25), with the source correction:
printed minimum over strict positive matrices is an infimum at singular inputs.
No full-rank or full-Schmidt-rank assumption is imposed. -/
theorem recovery_alberti_infimum
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] (rho : Mat (A × B)) (sigma : Mat (A × C))
    (purification : Mat ((A × C) × D))
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hpure : IsPure purification) (hmarginal : traceRight purification = sigma) :
    IsGLB {v : ℝ | ∃ r : Mat (A × B), ∃ q : Mat (A × D),
      r.PosDef ∧ q.PosDef ∧
      ((Matrix.of fun x y : (A × B) × D =>
        q (x.1.1, x.2) (y.1.1, y.2) * (1 : Mat B) x.1.2 y.1.2) -
        Matrix.kronecker r (1 : Mat D)).PosSemidef ∧ v = (rho * r⁻¹).trace.re * (marginalAD purification * q).trace.re}
      (generalizedRecoveryFidelity rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P75
