-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_algHom_matrix_injective_apply_eq_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit_of_pos
-- name    : QuaternionAlgebra.exists_algHom_matrix_injective_apply_eq_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/dbcdaa35-a3a6-555b-a837-f2f304066d67
-- title:
--   Embedding B into M₂(H') via a common quadratic subfield
-- statement:
--   Fix rationals $a,b,c,d$ and a natural number $q$ carrying a primality instance. Assume first that [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt c d q`](def/QuaternionAlgebra_EichlerOrder.html#L87) holds, i.e. $c<0$, $d<0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},c,d]\otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra (every nonzero element is a unit) precisely when $q$ lies in $v$. Assume second that for every height-one prime $v$ containing $q$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit. Assume third that $0<a$ or $0<b$. Then there exist rationals $t,s$, elements $x,w\in\mathbb{H}[\mathbb{Q},a,b]$, an element $y\in\mathbb{H}[\mathbb{Q},c,d]$ and a $\mathbb{Q}$-algebra homomorphism $\rho:\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{H}[\mathbb{Q},c,d])$ such that $t<0<s$; $x^2$ and $w^2$ are the images of $t$ and $s$ under the structure map of $\mathbb{H}[\mathbb{Q},a,b]$; $xw=-wx$; every $u\in\mathbb{H}[\mathbb{Q},a,b]$ is a $\mathbb{Q}$-linear combination $\alpha\cdot 1+\beta x+\gamma w+\delta (xw)$; $y^2$ is the image of $t$ in $\mathbb{H}[\mathbb{Q},c,d]$; $\rho$ is injective; and $\rho(x)=\begin{pmatrix} y&0\\ 0&-y\end{pmatrix}$, $\rho(w)=\begin{pmatrix} 0& s\\ 1&0\end{pmatrix}$, the entry $s$ meaning its image in $\mathbb{H}[\mathbb{Q},c,d]$.
--
--   This is the standard splitting of a quaternion algebra $B=\mathbb{H}[\mathbb{Q},a,b]$ that is ramified at the prime $q$ and has a positive structure constant, by embedding it into $2\times 2$ matrices over the definite quaternion algebra $H'=\mathbb{H}[\mathbb{Q},c,d]$ ramified exactly at $q$, using a quadratic subfield $\mathbb{Q}(\sqrt{t})$ common to $B$ and $H'$; the explicit images of the two anticommuting generators are part of the conclusion. It feeds the construction of embeddings and Eichler-order data for indefinite quaternion algebras ramified exactly at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_algHom_matrix_injective_apply_eq_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit_of_pos.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.exists_algHom_matrix_injective_apply_eq_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit_of_pos
    {a b c d : ℚ} (q : ℕ) [Fact q.Prime]
    (hH : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt c d q)
    (hBq : ∀ v : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∈ v.asIdeal →
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    (hab : 0 < a ∨ 0 < b) :
    ∃ (t s : ℚ) (x w : ℍ[ℚ, a, b]) (y : ℍ[ℚ, c, d]) (ρ : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]),
      t < 0 ∧ 0 < s ∧
      x * x = algebraMap ℚ ℍ[ℚ, a, b] t ∧ w * w = algebraMap ℚ ℍ[ℚ, a, b] s ∧ x * w = -(w * x) ∧
      (∀ u : ℍ[ℚ, a, b], ∃ α β γ δ : ℚ, u = α • 1 + β • x + γ • w + δ • (x * w)) ∧
      y * y = algebraMap ℚ ℍ[ℚ, c, d] t ∧
      Function.Injective ρ ∧
      ρ x = !![y, 0; 0, -y] ∧ ρ w = !![0, algebraMap ℚ ℍ[ℚ, c, d] s; 1, 0] := by sorry
