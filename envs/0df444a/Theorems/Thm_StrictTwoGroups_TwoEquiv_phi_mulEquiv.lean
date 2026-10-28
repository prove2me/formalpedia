-- Prove2me | Theorems.Thm_StrictTwoGroups_TwoEquiv_phi_mulEquiv
-- name    : StrictTwoGroups.TwoEquiv.phi_mulEquiv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:46.859277+00:00
-- url     : https://prove2.me/theorems/9894b7d7-9dcf-44b5-9f7e-cebc9ec43f06
-- title:
--   §2, p. 7, (11) — ϕ : G₁ → ker s ⋊ G₀, a ↦ (a·i(s a)⁻¹, s a), is a group isomorphism with inverse (h, g) ↦ h·i(g)
-- statement:
--   Let $\mathcal G$ be a strict 2-group and let $G_0$ act on the normal subgroup $\ker s\subseteq G_1$ by $g\mapsto\mathrm{Ad}_{ig}$, $\mathrm{Ad}_{ig}(h)=ig\,h\,(ig)^{-1}$. Then
--   $$\varphi:G_1\longrightarrow\ker s\rtimes G_0,\qquad a\longmapsto\bigl(a\,i(sa)^{-1},\ sa\bigr)$$
--   is a group isomorphism, and its inverse is $\varphi^{-1}(h,g)=h\,ig$.
--
--   The isomorphism transports the strict 2-group to the semidirect product on which the crossed module $T_0\mathcal G$ and the round trip $ST\mathcal G$ live; it is the component $\xi_{\mathcal G}$ of §6.
--
--   **Formalization Note** The statement asserts a `MulEquiv` whose forward map and inverse are given by the two formulas. It is stated for every `StrictTwoGroup` (groups, group morphisms $s,t,i$ with $s\,i=t\,i=\mathrm{id}$), without the composition axioms `IsStrictTwoGroup`, which the claim does not involve.
--
--   Differences from the source:
--   - generalization: $\mathcal G$ a strict 2-group → any `StrictTwoGroup` data, without `IsStrictTwoGroup`; reason: every strict 2-group is such data, so the Lean statement specializes to the paper's.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, p. 7, §2 isomorphism (11)

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_StrictTwoGroup

namespace StrictTwoGroups.TwoEquiv

universe u

/-- §2, p. 7, (11): the map `ϕ : G₁ → ker s ⋊ G₀`, `a ↦ (a · i(s a)⁻¹, s a)`, is a group
isomorphism with inverse `ϕ⁻¹(h, g) = h · i(g)`; the semidirect product is taken with respect to
the adjoint action `g ↦ Ad_{i g}` of `G₀` on `ker s`. -/
theorem phi_mulEquiv (G : StrictTwoGroup.{u}) :
    ∃ e : G.G1 ≃* (↥G.s.ker ⋊[MulAut.conjNormal.comp G.i] G.G0),
      (∀ a : G.G1, ((e a).left : G.G1) = a * (G.i (G.s a))⁻¹ ∧ (e a).right = G.s a) ∧
      ∀ x : ↥G.s.ker ⋊[MulAut.conjNormal.comp G.i] G.G0,
        e.symm x = (x.left : G.G1) * G.i x.right := by sorry

end StrictTwoGroups.TwoEquiv
