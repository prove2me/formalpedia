-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/17996776-f3d5-5e7c-b40d-27f3875e1541
-- title:
--   Special integral embedding of a maximal order into M₂(𝒪)
-- statement:
--   Let $q,q'$ be primes and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $B=\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completion $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division ring (every nonzero element is a unit) precisely when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order: it contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$, is finitely generated, and is not properly contained in any submodule with those four properties. Let $c,d\in\mathbb{Q}$ with $c<0$, $d<0$ be such that $H=\mathbb{H}[\mathbb{Q},c,d]$ has $H\otimes_{\mathbb{Q}}\mathbb{Q}_v$ a division ring precisely when $q\in v$, and let $O\subseteq H$ be a maximal order in the same sense. Then there is a $\mathbb{Q}$-algebra homomorphism $j:B\to M_2(H)$ all of whose matrix entries $j(m)_{il}$ lie in $O$ for $m\in\Lambda$, with the following property: for every field $F$ of characteristic $q$ and every map $\chi:O\to F$ sending $1$ to $1$, additive, and satisfying $\chi(xy)=\chi(x)\chi(y)$ whenever $x,y\in O$ (the product being taken in $O$), and for every $m\in\Lambda$ and every integer $n$ with $m+\overline{m}=n$ in $B$, one has $\chi(j(m)_{00})+\chi(j(m)_{11})=n\cdot 1_F$ in $F$.
--
--   This supplies the integral embedding of a maximal order of the indefinite quaternion algebra of discriminant $qq'$ into $2\times 2$ matrices over a maximal order of the definite algebra of discriminant $q$, together with the compatibility at $q$ of the reduced trace with the diagonal of the matrix: the embedding is 'special at $q$' in the sense that, modulo $q$, any multiplicative functional on $O$ computes the reduced trace from the two diagonal entries. It is used in the construction of fake elliptic curves over algebraically closed fields of characteristic $q$ in the Čerednik–Drinfeld part of the argument, via [`CerednikDrinfeld.QM.nonempty_fakeEllipticCurve_one_of_isAlgClosed_of_charP`](thm.html#CerednikDrinfeld.QM.nonempty_fakeEllipticCurve_one_of_isAlgClosed_of_charP).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField
open QuaternionAlgebra

theorem QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {c d : ℚ} (hH : IsDefiniteRamifiedExactlyAt c d q)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O) :
    ∃ (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
      (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O),
      ∀ (F : Type) [Field F] [CharP F q] (χ : ↥O → F),
        (∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, χ ⟨1, h⟩ = 1) →
        (∀ x y : ↥O, χ (x + y) = χ x + χ y) →
        (∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
          χ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = χ x * χ y) →
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          χ ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩ + χ ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩ = (n : F) := by sorry
