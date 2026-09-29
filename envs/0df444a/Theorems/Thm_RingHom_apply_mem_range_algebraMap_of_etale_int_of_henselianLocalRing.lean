-- Prove2me | Theorems.Thm_RingHom_apply_mem_range_algebraMap_of_etale_int_of_henselianLocalRing
-- name    : RingHom.apply_mem_range_algebraMap_of_etale_int_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/02d409fa-a4bd-5b85-84ad-680469318368
-- title:
--   Étale ℤ-algebras with prime residues lie in henselian subrings
-- statement:
--   Let $p$ be a prime and let $Pl$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense that the image of $p$ in $\overline{\mathbb{Q}}$ belongs to `Pl.nonunits`, the non-units of $Pl$ inside the ambient field (equivalently, $p$ lies in the maximal ideal of $Pl$). Let $R_h$ be a henselian local domain equipped with an algebra structure over $\overline{\mathbb{Q}}$ whose structure map is injective (`FaithfulSMul`), such that the image of $R_h$ in $\overline{\mathbb{Q}}$ is contained in $Pl$, and such that an element $x \in R_h$ lies in the maximal ideal of $R_h$ precisely when the valuation of its image under $Pl$ is $< 1$; thus $Pl$ dominates $R_h$. Let $E$ be a commutative ring which is an étale $\mathbb{Z}$-algebra, let $\iota : E \to \overline{\mathbb{Q}}$ be a ring homomorphism with $\iota(E) \subseteq Pl$, and let $\varphi_0 : E \to \mathbb{Z}/p$ be a ring homomorphism compatible with $\iota$ in the sense that for every $e \in E$ and every integer $n$ whose class mod $p$ equals $\varphi_0(e)$, the valuation of $\iota(e) - n$ under $Pl$ is $< 1$. The conclusion is that for every $e \in E$ the element $\iota(e)$ lies in the range of the structure map $R_h \to \overline{\mathbb{Q}}$.
--
--   This is the henselian half of the assertion that the decomposition ring of a place $\mathfrak{P}$ of $\overline{\mathbb{Q}}$ above $p$ is minimal among henselian local domains dominated by $\mathfrak{P}$, the étale $\mathbb{Z}$-algebra $E$ playing the role of an étale neighbourhood of $\mathbb{Z}_{(p)}$. It is used by [`ValuationSubring.mem_range_algebraMap_of_mem_inf_fixedField_decompositionSubgroup_of_henselianLocalRing`](thm.html#ValuationSubring.mem_range_algebraMap_of_mem_inf_fixedField_decompositionSubgroup_of_henselianLocalRing), and its proof rests on the lifting of a residue-field point of an étale algebra over a henselian local ring, [`HenselianLocalRing.exists_algHom_lift_of_etale`](thm.html#HenselianLocalRing.exists_algHom_lift_of_etale).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_apply_mem_range_algebraMap_of_etale_int_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem RingHom.apply_mem_range_algebraMap_of_etale_int_of_henselianLocalRing
    (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    (E : Type) [CommRing E] [Algebra.Etale ℤ E]
    (ι : E →+* AlgebraicClosure ℚ) (hι : ∀ e : E, ι e ∈ Pl)
    (φ₀ : E →+* ZMod p) (hφ₀ : ∀ (e : E) (n : ℤ), (n : ZMod p) = φ₀ e → Pl.valuation (ι e - n) < 1) :
    ∀ e : E, ι e ∈ Set.range (algebraMap Rh (AlgebraicClosure ℚ)) := by sorry
