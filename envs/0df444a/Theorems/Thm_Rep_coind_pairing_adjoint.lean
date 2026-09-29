-- Prove2me | Theorems.Thm_Rep_coind_pairing_adjoint
-- name    : Rep.coind_pairing_adjoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/571e3aff-82d1-5b0c-850a-8e604eb85cc1
-- title:
--   Adjointness of the coinduced pairing under units and traces
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and $S \le G$ a subgroup of finite index; let $M$, $D$, $N$ be objects of `Rep k G`. Let $\varphi : M \to D \to N$ be a $k$-bilinear map which is equivariant in the sense of [`Rep.IsEquivariantBilinear`](def/GroupCohomology_CupProduct.html#L13), i.e. $\varphi(\rho_M(g)a, \rho_D(g)b) = \rho_N(g)\varphi(a,b)$ for all $g \in G$. Write $\mathrm{CoInd}\,\mathrm{Res}\,X$ for `Rep.coind S.subtype (Rep.res S.subtype X)`, whose elements are functions $f : G \to X$ with $f(sh) = \rho_X(s)f(h)$ for $s \in S$. Assume given morphisms of representations $\iota_M : M \to \mathrm{CoInd}\,\mathrm{Res}\,M$ and $\iota_D : D \to \mathrm{CoInd}\,\mathrm{Res}\,D$ with $(\iota_M m)(g) = \rho_M(g)m$ and $(\iota_D d)(g) = \rho_D(g)d$; morphisms $\tau_M$, $\tau_D$, $\tau_N$ from $\mathrm{CoInd}\,\mathrm{Res}\,X$ to $X$ ($X = M, D, N$) given by the finite sums $\tau_X(f) = \sum^{\mathrm{f}}_{q \in G/S} \rho_X(\bar q)\,f(\bar q^{-1})$ over chosen coset representatives $\bar q$; and a $k$-bilinear $\Psi : \mathrm{CoInd}\,\mathrm{Res}\,M \to \mathrm{CoInd}\,\mathrm{Res}\,D \to N$ such that $\Psi(f,g) = \tau_N(w)$ whenever $w \in \mathrm{CoInd}\,\mathrm{Res}\,N$ satisfies $w(h) = \varphi(f(h), g(h))$ for all $h \in G$. The conclusion is the conjunction of the two identities $\Psi(\iota_M m, y) = \varphi(m, \tau_D y)$ for all $m \in M$ and $y \in \mathrm{CoInd}\,\mathrm{Res}\,D$, and $\Psi(x, \iota_D d) = \varphi(\tau_M x, d)$ for all $x \in \mathrm{CoInd}\,\mathrm{Res}\,M$ and $d \in D$.
--
--   These are the two adjointness (Frobenius-reciprocity type) identities relating a pairing $\varphi$ on $(M,D)$ to the induced pairing $\Psi$ on the coinduced representations, with respect to the unit and trace maps of coinduction along a finite-index subgroup. They feed the retract argument by which a duality statement for $\mathrm{CoInd}\,\mathrm{Res}$ descends to one for the original modules, and are used in the proofs that the duality maps [`groupCohomology.bijective_theta_dualTwist_of_res`](thm.html#groupCohomology.bijective_theta_dualTwist_of_res) and [`groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen`](thm.html#groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen) are bijective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_coind_pairing_adjoint.lean

import Mathlib
import Definitions.Def_GroupCohomology_CupProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem Rep.coind_pairing_adjoint {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) [S.FiniteIndex] {M D N : Rep.{u} k G}
    (φ : M →ₗ[k] D →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear M D N φ)
    (ιM : M ⟶ Rep.coind S.subtype (Rep.res S.subtype M))
    (hιM : ∀ (m : M) (g : G), ((ιM.hom m : Rep.coind S.subtype (Rep.res S.subtype M)) : G → M) g = M.ρ g m)
    (τM : Rep.coind S.subtype (Rep.res S.subtype M) ⟶ M)
    (hτM : ∀ f : Rep.coind S.subtype (Rep.res S.subtype M),
      τM.hom f = ∑ᶠ q : G ⧸ S, M.ρ q.out ((f : G → M) (q.out)⁻¹))
    (ιD : D ⟶ Rep.coind S.subtype (Rep.res S.subtype D))
    (hιD : ∀ (d : D) (g : G), ((ιD.hom d : Rep.coind S.subtype (Rep.res S.subtype D)) : G → D) g = D.ρ g d)
    (τD : Rep.coind S.subtype (Rep.res S.subtype D) ⟶ D)
    (hτD : ∀ f : Rep.coind S.subtype (Rep.res S.subtype D),
      τD.hom f = ∑ᶠ q : G ⧸ S, D.ρ q.out ((f : G → D) (q.out)⁻¹))
    (τN : Rep.coind S.subtype (Rep.res S.subtype N) ⟶ N)
    (hτN : ∀ f : Rep.coind S.subtype (Rep.res S.subtype N),
      τN.hom f = ∑ᶠ q : G ⧸ S, N.ρ q.out ((f : G → N) (q.out)⁻¹))
    (Ψ : Rep.coind S.subtype (Rep.res S.subtype M) →ₗ[k] Rep.coind S.subtype (Rep.res S.subtype D) →ₗ[k] N)
    (hΨ : ∀ (f : Rep.coind S.subtype (Rep.res S.subtype M)) (g : Rep.coind S.subtype (Rep.res S.subtype D))
      (w : Rep.coind S.subtype (Rep.res S.subtype N)),
      (∀ h : G, (w : G → N) h = φ ((f : G → M) h) ((g : G → D) h)) → Ψ f g = τN.hom w) :
    (∀ (m : M) (y : Rep.coind S.subtype (Rep.res S.subtype D)), Ψ (ιM.hom m) y = φ m (τD.hom y)) ∧
    (∀ (x : Rep.coind S.subtype (Rep.res S.subtype M)) (d : D), Ψ x (ιD.hom d) = φ (τM.hom x) d) := by sorry
