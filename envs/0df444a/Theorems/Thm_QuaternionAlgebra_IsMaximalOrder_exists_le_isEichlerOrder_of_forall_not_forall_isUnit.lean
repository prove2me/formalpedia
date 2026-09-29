-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_le_isEichlerOrder_of_forall_not_forall_isUnit
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_le_isEichlerOrder_of_forall_not_forall_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/612bd18e-53c6-57ae-8643-3c983fa9466f
-- title:
--   Eichler orders of level N inside a maximal order
-- statement:
--   Let $a,b$ be non-zero rationals and work in the rational quaternion algebra $\mathbb H[\mathbb Q,a,b]$. Here an *order* is a $\mathbb Z$-submodule $\Lambda$ containing $1$, closed under multiplication, whose $\mathbb Q$-span is the whole algebra and which is finitely generated; it is *maximal* if every order containing it equals it. Let $\Lambda_1$ be a maximal order and $N$ a non-zero natural number, and assume that for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ whose ideal contains the image of $N$, it fails that every non-zero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ (the $v$-adic completion) is a unit; that is, the completion at each prime dividing $N$ is not a division ring. The conclusion asserts the existence of a $\mathbb Z$-submodule $\Lambda\le\Lambda_1$ which is an Eichler order of level $N$ in the sense of the project: there are maximal orders $\Lambda_1',\Lambda_2'$ with $\Lambda=\Lambda_1'\cap\Lambda_2'$ and with the relative index of the additive subgroup of $\Lambda$ in that of $\Lambda_1'$ equal to $N$. Note that the two maximal orders realising $\Lambda$ as an intersection are quantified existentially, the given $\Lambda_1$ being constrained only by $\Lambda\le\Lambda_1$.
--
--   This is the classical existence of Eichler orders of arbitrary level $N$ inside a prescribed maximal order of a rational quaternion algebra, under the necessary local condition that the algebra split at every prime dividing $N$. It is used by [`QuaternionAlgebra.exists_isIndefiniteRamifiedExactlyAt_isMaximalOrder_isEichlerOrder_splitting`](thm.html#QuaternionAlgebra.exists_isIndefiniteRamifiedExactlyAt_isMaximalOrder_isEichlerOrder_splitting), which produces an indefinite quaternion algebra ramified at a prescribed set of places together with a maximal order and an Eichler order of the required level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_le_isEichlerOrder_of_forall_not_forall_isUnit.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsMaximalOrder.exists_le_isEichlerOrder_of_forall_not_forall_isUnit
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (h₁ : QuaternionAlgebra.IsMaximalOrder Λ₁)
    (N : ℕ) (hN : N ≠ 0)
    (hsplit : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal →
      ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ∃ Λ : Submodule ℤ ℍ[ℚ, a, b], Λ ≤ Λ₁ ∧ QuaternionAlgebra.IsEichlerOrder Λ N := by sorry
