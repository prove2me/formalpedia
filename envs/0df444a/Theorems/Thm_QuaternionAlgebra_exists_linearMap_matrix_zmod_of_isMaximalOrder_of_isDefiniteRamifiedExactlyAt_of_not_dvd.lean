-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt_of_not_dvd
-- name    : QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/affc94c1-0f29-540c-a1a4-36cb794e0325
-- title:
--   Reduction of a definite maximal order mod N is M₂(ℤ/N)
-- statement:
--   Let $c,d$ be rational numbers and $r$ a prime. Assume [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt c d r`](def/QuaternionAlgebra_EichlerOrder.html#L87), i.e. $c<0$, $d<0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the tensor product $\mathbb{H}[\mathbb{Q},c,d]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ (the $v$-adic completion) has all its nonzero elements invertible precisely when $r$ lies in the prime ideal $v$. Let $O$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},c,d]$ which is a maximal order, that is: $1\in O$, $O$ is closed under multiplication, the $\mathbb{Q}$-span of $O$ is the whole algebra, $O$ is finitely generated over $\mathbb{Z}$, and any order containing $O$ equals $O$. Let $N$ be a nonzero natural number with $r\nmid N$. Then there exists a $\mathbb{Z}$-linear map $\varphi : O \to M_2(\mathbb{Z}/N)$ such that $\varphi(1)=1$; for all $x,y\in O$, $\varphi$ applied to the product $xy$ (viewed in $O$) equals $\varphi(x)\varphi(y)$; $\varphi$ is surjective; and for $x\in O$ one has $\varphi(x)=0$ if and only if $x=N\cdot y$ in $\mathbb{H}[\mathbb{Q},c,d]$ for some $y\in O$. Thus $\varphi$ identifies $O/NO$ with $M_2(\mathbb{Z}/N)$, the ring structure being expressed by the unit and multiplicativity clauses rather than by a ring homomorphism.
--
--   This is the statement that a maximal order in a definite rational quaternion algebra ramified exactly at $r$ becomes isomorphic to $M_2(\mathbb{Z}/N)$ after reduction modulo any $N$ prime to $r$, obtained from the prime-power case together with the Chinese remainder theorem. It is used in the Čerednik–Drinfeld part of the construction, in [`CerednikDrinfeld.QM.exists_equiv_torsion_and_forall_pushPt_eq_mulVec_of_forall_exists_eq_of_isMaximalOrder`](thm.html#CerednikDrinfeld.QM.exists_equiv_torsion_and_forall_pushPt_eq_mulVec_of_forall_exists_eq_of_isMaximalOrder), to produce a two-dimensional $\mathbb{Z}/N$-representation of the order acting on $N$-torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt_of_not_dvd.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt_of_not_dvd
    {c d : ℚ} {r : ℕ} [Fact r.Prime]
    (hH' : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt c d r)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : QuaternionAlgebra.IsMaximalOrder O)
    (N : ℕ) [NeZero N] (hrN : ¬ r ∣ N) :
    ∃ φ : ↥O →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod N),
      (∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
          φ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = φ x * φ y) ∧
      Function.Surjective φ ∧
      (∀ x : ↥O, φ x = 0 ↔ ∃ y : ↥O, (x : ℍ[ℚ, c, d]) = (N : ℚ) • (y : ℍ[ℚ, c, d])) := by sorry
