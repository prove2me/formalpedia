-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P75_ordinaryRecovery_product_optimum
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P75.ordinaryRecovery_product_optimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:49:56.852557+00:00
-- url     : https://prove2.me/theorems/59fc2466-26e6-4d1f-bf25-133aee910f49
-- title:
--   Ordinary recovery fidelity and an optimal product recovery
-- statement:
--   For density operators $\rho_{ABC}$ and $\tau_{A'B'C'}$ on arbitrary finite-dimensional nonzero complex systems, define $F(A;B|C)_\rho=\sup_\Gamma F(\rho_{ABC},(\mathrm{id}_B\otimes\Gamma)(\rho_{BC}))$, where $\Gamma:C\to AC$ is CPTP and $F$ is squared fidelity. Then
--
--   $$
--   F(AA';BB'|CC')_{\rho\otimes\tau}=F(A;B|C)_\rho F(A';B'|C')_\tau.
--   $$
--
--   There exist optimal individual CPTP maps $\Gamma:C\to AC$ and $\Lambda:C'\to A'C'$ whose product $\Gamma\otimes\Lambda$ is an optimal joint recovery for $\rho\otimes\tau$. The joint optimization still ranges over every joint CPTP map. This gives an attained product optimum without asserting that every optimizer has product form.
-- source:
--   The Fidelity of Recovery is Multiplicative, arXiv:1502.07973v2, PDF p. 2, Introduction, (7) and following sentence

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

/-- PDF p.2, (7) and following sentence: ordinary FoR is multiplicative
and SOME optimal joint recovery is a product of optimal individual maps. -/
theorem ordinaryRecovery_product_optimum
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty Ap] [Nonempty Bp] [Nonempty Cp] (rho : Mat (B × (A × C)))
    (tau : Mat (Bp × (Ap × Cp))) (hrho : IsDensityMatrix rho) (htau : IsDensityMatrix tau) :
    ordinaryRecovery (ordinaryTensor rho tau) = ordinaryRecovery rho * ordinaryRecovery tau ∧
    ∃ f : Superop C (A × C), ∃ g : Superop Cp (Ap × Cp),
      IsChannel f ∧ IsChannel g ∧ IsChannel (productRecovery f g) ∧
      fidelity rho (recovered rho f) = ordinaryRecovery rho ∧
      fidelity tau (recovered tau g) = ordinaryRecovery tau ∧
      fidelity (ordinaryTensor rho tau)
        (recovered (ordinaryTensor rho tau) (productRecovery f g)) =
          ordinaryRecovery (ordinaryTensor rho tau) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P75
