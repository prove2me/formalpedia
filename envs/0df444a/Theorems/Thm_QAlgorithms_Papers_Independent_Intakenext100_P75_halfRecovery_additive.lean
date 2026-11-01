-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P75_halfRecovery_additive
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P75.halfRecovery_additive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:52:17.150444+00:00
-- url     : https://prove2.me/theorems/861be395-8da7-4b6b-8d55-83bf0a1215a4
-- title:
--   Additivity of order-one-half relative entropy of recovery
-- statement:
--   For density operators define the sandwiched order-one-half divergence in bits by $D_{1/2}(\rho\|\sigma)=-\log_2 F(\rho,\sigma)$, where $F$ is squared fidelity; its value is $+\infty$ exactly when fidelity is zero. For a tripartite density operator $\rho_{ABC}$ on finite-dimensional nonzero complex systems and any positive integer $n$,
--
--   $$
--   \min_{\Gamma:C^n\to A^nC^n}
--   D_{1/2}\!\left(\rho_{ABC}^{\otimes n}\middle\|(\mathrm{id}_{B^n}\otimes\Gamma)(\rho_{BC}^{\otimes n})\right)
--   =n\min_{\Lambda:C\to AC}
--   D_{1/2}\!\left(\rho_{ABC}\middle\|(\mathrm{id}_B\otimes\Lambda)(\rho_{BC})\right).
--   $$
--
--   Both domains contain every CPTP map of the indicated type, and both minima are attained. No support-containment guard is imposed for positive fidelity. This expresses multiplicativity as additivity of the relative entropy of recovery.
-- source:
--   The Fidelity of Recovery is Multiplicative, arXiv:1502.07973v2, PDF p. 7, Conclusion, (49)

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

/-- PDF p.7, (49): additivity of order-one-half recovery divergence for
positive copy counts; the minimum values are attained by actual CPTP maps. -/
theorem halfRecovery_additive
    [Nonempty A] [Nonempty B] [Nonempty C] (rho : Mat (B × (A × C))) (hrho : IsDensityMatrix rho)
    (n : ℕ) (hn : 0 < n) :
    halfRecovery (ordinaryCopies rho n) = (n : EReal) * halfRecovery rho ∧
    (∃ f : Superop C (A × C), IsChannel f ∧
      halfRenyi rho (recovered rho f) = halfRecovery rho) ∧
    (∃ f : Superop (Fin n → C) ((Fin n → A) × (Fin n → C)), IsChannel f ∧
      halfRenyi (ordinaryCopies rho n) (recovered (ordinaryCopies rho n) f) =
        halfRecovery (ordinaryCopies rho n)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P75
