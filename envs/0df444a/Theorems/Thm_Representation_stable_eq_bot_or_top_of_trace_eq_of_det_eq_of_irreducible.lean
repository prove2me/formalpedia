-- Prove2me | Theorems.Thm_Representation_stable_eq_bot_or_top_of_trace_eq_of_det_eq_of_irreducible
-- name    : Representation.stable_eq_bot_or_top_of_trace_eq_of_det_eq_of_irreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/81e6005c-56d9-568a-9b40-842bb2232ab7
-- title:
--   Irreducibility transfers along equal traces and determinants
-- statement:
--   Let $k$ be a field, $G$ a group, and let $V$, $V_2$ be $k$-vector spaces carrying representations $\rho_1 \colon G \to \mathrm{GL}(V)$ and $\rho_2 \colon G \to \mathrm{GL}(V_2)$, each of $k$-dimension $2$ (as `Module.finrank`). Assume that $\rho_1$ is irreducible in the sense that every $k$-subspace $W \subseteq V$ with $\rho_1(g)v \in W$ for all $g \in G$ and all $v \in W$ is either $\bot$ or $\top$; and assume that the two representations have matching characteristic data pointwise, namely $\mathrm{tr}(\rho_1 g) = \mathrm{tr}(\rho_2 g)$ and $\det(\rho_1 g) = \det(\rho_2 g)$ for every $g \in G$, where trace and determinant are those of the $k$-linear endomorphisms. The conclusion is that $\rho_2$ is irreducible in the same sense: every $k$-subspace $W \subseteq V_2$ stable under all $\rho_2(g)$, in the pointwise formulation that $\rho_2(g)v \in W$ whenever $v \in W$, equals $\bot$ or $\top$. No hypothesis is imposed on the characteristic or the size of $k$, on $G$, or on semisimplicity.
--
--   This is the two-dimensional consumer form of the Brauer–Nesbitt principle: a representation with the same traces and determinants as an irreducible two-dimensional representation can have no stable line, so the pair (trace, determinant) detects irreducibility in dimension $2$. It is used in the level-lowering part of the argument, via [`RibetIrr.span_range_baseChange_eq_top_of_companion`](thm.html#RibetIrr.span_range_baseChange_eq_top_of_companion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_stable_eq_bot_or_top_of_trace_eq_of_det_eq_of_irreducible.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Representation.stable_eq_bot_or_top_of_trace_eq_of_det_eq_of_irreducible {k G V V₂ : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup V₂] [Module k V₂]
    (ρ₁ : Representation k G V) (ρ₂ : Representation k G V₂)
    (hfr₁ : Module.finrank k V = 2) (hfr₂ : Module.finrank k V₂ = 2)
    (hirr : ∀ W : Submodule k V, (∀ g, ∀ v ∈ W, ρ₁ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ g, LinearMap.trace k V (ρ₁ g) = LinearMap.trace k V₂ (ρ₂ g))
    (hdet : ∀ g, LinearMap.det (ρ₁ g) = LinearMap.det (ρ₂ g)) :
    ∀ W : Submodule k V₂, (∀ g, ∀ v ∈ W, ρ₂ g v ∈ W) → W = ⊥ ∨ W = ⊤ := by sorry
