-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_span_range_map_algebraMap_eq_top_of_isMaximalOrder
-- name    : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.span_range_map_algebraMap_eq_top_of_isMaximalOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/123c9590-7d7a-5855-8e9c-514bddedcbec
-- title:
--   Complexified image of a maximal order spans M₂(ℂ)
-- statement:
--   Let $q,q'$ be primes and $a,b$ rational numbers, and let $B=\mathbb{H}[\mathbb{Q},a,b]$ be the quaternion algebra over $\mathbb{Q}$ with $i^2=a$, $j^2=b$. Assume `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: $0<a$ or $0<b$, and for every place $v$ in the height one spectrum of the ring of integers of $\mathbb{Q}$, the algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ (the adic completion at $v$) has every nonzero element a unit precisely when the image of $q$ or of $q'$ lies in the prime ideal $v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $B$ which is a maximal order, i.e. $1\in\Lambda$, $\Lambda$ is closed under multiplication, the $\mathbb{Q}$-span of $\Lambda$ is all of $B$, $\Lambda$ is finitely generated over $\mathbb{Z}$, and every submodule with these four properties containing $\Lambda$ equals $\Lambda$. Let $\iota : B \to M_2(\mathbb{R})$ be an injective homomorphism of $\mathbb{Q}$-algebras. Then the $\mathbb{C}$-linear span of the set of matrices obtained by applying $\iota$ to the elements of $\Lambda$ and mapping the entries along $\mathbb{R}\to\mathbb{C}$ is the whole of $M_2(\mathbb{C})$.
--
--   An order in a quaternion algebra is a full-rank lattice, so its image under a real splitting $\iota$ remains a $\mathbb{C}$-basis of the $4$-dimensional algebra $M_2(\mathbb{C})$ after complexification; the proof uses that $B$ is a division algebra, which follows from the ramification hypothesis. The statement is used in the construction of the uniformisation of families of fake elliptic curves in the Čerednik–Drinfel'd setting, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLocalHom_differentiableOn_uniformization_family_near_zero`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLocalHom_differentiableOn_uniformization_family_near_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_span_range_map_algebraMap_eq_top_of_isMaximalOrder.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open QuaternionAlgebra
open scoped Quaternion

theorem QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.span_range_map_algebraMap_eq_top_of_isMaximalOrder
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    Submodule.span ℂ (Set.range fun x : ↥Λ => (ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)) = ⊤ := by sorry
