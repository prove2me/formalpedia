-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_linearMap_tateModule_apply_eq_of_addMonoidHom_points
-- name    : PDivisibleGroup.exists_linearMap_tateModule_apply_eq_of_addMonoidHom_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/1612a7ca-4819-5825-ba9f-e10e214370c2
-- title:
--   Functoriality of Tate modules under additive maps of points
-- statement:
--   Fix a prime $p$, a commutative ring $R$, a field $L$ that is an $R$-algebra, and natural numbers $h, h'$. Let $G$ be a $p$-divisible group over $R$ of height datum $(p,h)$ and $H$ one of datum $(p,h')$, that is, each consists of a sequence of finite free cocommutative $R$-Hopf algebras `level v` with $\operatorname{rank}_R(\mathrm{level}\ v) = p^{vh}$ (resp. $p^{vh'}$), together with surjective coalgebra-algebra maps $\mathrm{level}(v+1) \to \mathrm{level}\ v$ whose kernels are the $p^v$-torsion ideals. Write $G.\mathrm{Points}\ L$ for the direct limit of the additive groups attached to the $L$-points $\mathrm{Hom}_{R\text{-alg}}(\mathrm{level}\ v, L)$ under convolution, along the maps induced by the transition maps, and similarly for $H$. Let $F : G.\mathrm{Points}\ L \to H.\mathrm{Points}\ L$ be any additive group homomorphism. Then there exists a $\mathbb{Z}_p$-linear map $TF$ from [`TateModule p (G.Points L)`](def/EllipticCurve_TateModule.html#L15) to [`TateModule p (H.Points L)`](def/EllipticCurve_TateModule.html#L15) — where for an abelian group $M$, [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) is the subgroup of sequences $x : \mathbb{N} \to M$ satisfying $p^n \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$ for all $n$ — such that for every $x$ in the Tate module of $G.\mathrm{Points}\ L$ and every $n$, the $n$-th component of $TF(x)$ equals $F(x_n)$.
--
--   This is the functoriality of the Tate module construction on the $L$-points of a $p$-divisible group: an additive map of point groups induces a $\mathbb{Z}_p$-linear map of Tate modules, computed componentwise. It feeds into the full-faithfulness statement for $p$-divisible groups over rings of integers, being cited by [`PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_ringOfIntegers`](thm.html#PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_ringOfIntegers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_linearMap_tateModule_apply_eq_of_addMonoidHom_points.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.exists_linearMap_tateModule_apply_eq_of_addMonoidHom_points
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] {L : Type} [Field L] [Algebra R L]
    {h h' : ℕ} (G : PDivisibleGroup R p h) (H : PDivisibleGroup R p h') (F : G.Points L →+ H.Points L) :
    ∃ TF : TateModule p (G.Points L) →ₗ[ℤ_[p]] TateModule p (H.Points L),
      ∀ (x : TateModule p (G.Points L)) (n : ℕ),
        ((TF x : TateModule p (H.Points L)) : ℕ → H.Points L) n = F ((x : ℕ → G.Points L) n) := by sorry
