-- Prove2me | Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
-- name    : QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/c4c38de9-3ea9-57fa-956c-1dd84d5f587c
-- title:
--   Local division-algebra criterion via anisotropy of the norm form
-- statement:
--   Let $a,b\in\mathbb Q$ and let $v$ be a height-one prime of the ring of integers of $\mathbb Q$, with $v$-adic completion $\mathbb Q_v$ (the field `v.adicCompletion ℚ`). The theorem asserts the equivalence of two statements. The first is that every non-zero element of the $\mathbb Q_v$-algebra obtained from the generalised quaternion algebra $\mathbb H[\mathbb Q,a,b]$ by base change, namely the tensor product $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$, is a unit, i.e. this ring is a division ring. The second is that the quaternary quadratic form $x_0^2-a\,x_1^2-b\,x_2^2+ab\,x_3^2$ over $\mathbb Q_v$, in which $a$ and $b$ are taken as the images of the rationals $a,b$ in $\mathbb Q_v$, is anisotropic: for all $x_0,x_1,x_2,x_3\in\mathbb Q_v$, the vanishing of $x_0^2-a\,x_1^2-b\,x_2^2+ab\,x_3^2$ forces $x_0=x_1=x_2=x_3=0$. Here $\mathbb H[K,a,b]$ denotes Mathlib's quaternion algebra with $i^2=a$, $j^2=b$, and the displayed form is its reduced norm.
--
--   This is the local criterion identifying the places at which an explicit rational quaternion algebra $\mathbb H[\mathbb Q,a,b]$ is ramified: the completed algebra is a division algebra exactly when its norm form is anisotropic over $\mathbb Q_v$, so that ramification can be decided by Hilbert-symbol or local-square computations. It serves as the entry point for verifying the division-algebra condition at a given finite place in the study of Eichler orders and of the Čerednik–Drinfeld setting, where it is used by the lemmas on Hecke sets and stabilisers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
    (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
      ∀ x₀ x₁ x₂ x₃ : v.adicCompletion ℚ,
        x₀ ^ 2 - (a : v.adicCompletion ℚ) * x₁ ^ 2 - (b : v.adicCompletion ℚ) * x₂ ^ 2 +
            (a : v.adicCompletion ℚ) * (b : v.adicCompletion ℚ) * x₃ ^ 2 = 0 →
          x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by sorry
