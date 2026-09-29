-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_forall_point_valuation_cartierTranspose_sub_pow_lt_one_of_comp_eq_comp_verschiebung_of_bijective_tensorProduct_zmodp
-- name    : PDivisibleGroup.CartierDuality.forall_point_valuation_cartierTranspose_sub_pow_lt_one_of_comp_eq_comp_verschiebung_of_bijective_tensorProduct_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/8b35080d-9484-59bc-93cf-a9c68cda31b7
-- title:
--   Cartier transpose as Frobenius on integral ε-supported points
-- statement:
--   Fix a prime $p$, a valuation subring $\mathfrak P$ of $\overline{\mathbb Q}$, and a henselian local domain $R_h$ with an algebra structure on $\overline{\mathbb Q}$ whose scalar action is faithful, such that every $\mathrm{algebraMap}$-image of $R_h$ lies in $\mathfrak P$, the maximal ideal of $R_h$ consists exactly of the elements whose image has $\mathfrak P$-valuation $<1$, and an $R_h$-algebra structure on $\mathbb Z/p$ whose kernel is described by the same condition. Let $\mathcal G$ be a $p$-divisible group over $R_h$ of height $h$ (a system of finite free cocommutative Hopf algebras $\mathcal G.\mathrm{level}\,v$ with surjective transitions, $\mathrm{finrank} = p^{vh}$ and kernels the $p^v$-torsion ideals), $\mathcal G'$ another such together with a Cartier duality $\mathrm{Dual}$, i.e. bialgebra isomorphisms $\mathcal G'.\mathrm{level}\,v \cong \mathrm{CartierDual}\,R_h\,(\mathcal G.\mathrm{level}\,v)$ compatible with the transitions and multiplication by $p$. Fix $v$ and bialgebra endomorphisms $f,\varepsilon$ of $\mathcal G.\mathrm{level}\,v$. Write $B := \mathbb Z/p \otimes_{R_h} \mathcal G.\mathrm{level}\,v$ and let $V_B$ be a bialgebra endomorphism of $B$ whose transpose is the $p$-th power map on the Cartier dual: $\varphi(V_B b) = (\varphi^p)(b)$ for all functionals $\varphi$ and all $b$. Let $G_c, G_e$ be finite cocommutative Hopf algebras over $\mathbb Z/p$ with $G_c$ local and $G_e$ reduced, with surjective bialgebra maps $q_c : B \to G_c$, $\pi_e : B \to G_e$, and a bijective bialgebra map $\Theta : B \to G_c \otimes_{\mathbb Z/p} G_e$ satisfying $\Theta = (q_c \otimes \pi_e) \circ \Delta$. Assume the identity $q_c \circ f^\flat \circ \varepsilon^\flat = q_c \circ V_B \circ \varepsilon^\flat$ of algebra maps, where $f^\flat, \varepsilon^\flat$ are the base changes of $f,\varepsilon$ to $B$. Then for every point $\psi$ of $\mathcal G'$ at level $v$ with values in $\overline{\mathbb Q}$, i.e. an $R_h$-algebra map $\mathcal G'.\mathrm{level}\,v \to \overline{\mathbb Q}$, such that all values $\psi(a)$ lie in $\mathfrak P$ and such that $\psi \circ \varepsilon^{t} = \psi$, where $\varepsilon^{t}$ denotes $\mathrm{CartierDual.map}\,\varepsilon$ transported through $\mathrm{Dual.equiv}\,v$, one has, for every $a \in \mathcal G'.\mathrm{level}\,v$, that the $\mathfrak P$-valuation of $\psi(f^{t}a) - \psi(a)^p$ is $<1$, with $f^{t}$ the analogously transported $\mathrm{CartierDual.map}\,f$.
--
--   This is the Hopf-algebra core of the ordinary Eichler–Shimura congruence: a Verschiebung identity on the connected factor of the special fibre forces the Cartier transpose of $f$ to act on integral, $\varepsilon$-supported dual points as the $p$-power (Frobenius) twist modulo the maximal ideal of the chosen place. It is used in the construction of the unit and congruence data attached to the Néron object of a modular curve at $p$ on the ordinary part, where $f$ and $\varepsilon$ come from a Hecke operator $U_p$, a diamond operator and an ordinary idempotent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_forall_point_valuation_cartierTranspose_sub_pow_lt_one_of_comp_eq_comp_verschiebung_of_bijective_tensorProduct_zmodp.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open IsLocalRing

theorem PDivisibleGroup.CartierDuality.forall_point_valuation_cartierTranspose_sub_pow_lt_one_of_comp_eq_comp_verschiebung_of_bijective_tensorProduct_zmodp
    (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    {h : ℕ} (𝒢 : PDivisibleGroup Rh p h) {𝒢' : PDivisibleGroup Rh p h} (Dual : 𝒢.CartierDuality 𝒢')
    (v : ℕ)

    (f ε : 𝒢.level v →ₐc[Rh] 𝒢.level v)

    (VB : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v)
    (hVB : ∀ (φ : CartierDual (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v)) (b : ZMod p ⊗[Rh] 𝒢.level v),
      φ (VB b) = (φ ^ p) b)

    (Gc : Type) [CommRing Gc] [HopfAlgebra (ZMod p) Gc] [Coalgebra.IsCocomm (ZMod p) Gc] [Module.Finite (ZMod p) Gc]
    (Ge : Type) [CommRing Ge] [HopfAlgebra (ZMod p) Ge] [Coalgebra.IsCocomm (ZMod p) Ge] [Module.Finite (ZMod p) Ge]
    (qc : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] Gc) (πe : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] Ge)
    (Θ : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] Gc ⊗[ZMod p] Ge)
    (hGc : IsLocalRing Gc) (hGe : IsReduced Ge)
    (hqc : Function.Surjective qc) (hπe : Function.Surjective πe) (hΘ : Function.Bijective Θ)
    (hΘΔ : ∀ b, Θ b = Algebra.TensorProduct.map (qc : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Gc)
      (πe : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Ge) (Coalgebra.comul (R := ZMod p) b))

    (hV : (qc : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Gc).comp
        (((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) f).comp
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ε) :
            ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) :
          ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) =
      (qc : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Gc).comp
        ((VB.comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ε) :
            ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) :
          ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v)) :
    ∀ ψ : 𝒢'.Point (AlgebraicClosure ℚ) v,

      (∀ a : 𝒢'.level v, PDivisibleGroup.Point.toAlgHom ψ a ∈ Pl) →

      (PDivisibleGroup.Point.toAlgHom ψ).comp (((Dual.equiv v).symm : CartierDual Rh (𝒢.level v) →ₐc[Rh] 𝒢'.level v).comp
          ((CartierDual.map ε).comp (Dual.equiv v : 𝒢'.level v →ₐc[Rh] CartierDual Rh (𝒢.level v))) :
            𝒢'.level v →ₐ[Rh] 𝒢'.level v) = PDivisibleGroup.Point.toAlgHom ψ →

      ∀ a : 𝒢'.level v,
        Pl.valuation ((PDivisibleGroup.Point.toAlgHom ψ).comp (((Dual.equiv v).symm : CartierDual Rh (𝒢.level v) →ₐc[Rh] 𝒢'.level v).comp
          ((CartierDual.map f).comp (Dual.equiv v : 𝒢'.level v →ₐc[Rh] CartierDual Rh (𝒢.level v))) :
            𝒢'.level v →ₐ[Rh] 𝒢'.level v) a -
          PDivisibleGroup.Point.toAlgHom ψ a ^ p) < 1 := by sorry
