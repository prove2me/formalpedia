-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_Supplement_network_base
-- name    : SteinitzExchange.Duality.Supplement.network_base
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:30:20.148849+00:00
-- url     : https://prove2.me/theorems/41f85be3-886e-4a5b-9973-0b65a6a7f9c7
-- title:
--   Lemma 7.1 — network induction preserves the base-set exchange axiom (B1)
-- statement:
--   Let $G=(V,A;V^+,V^-)$ be a finite directed graph with disjoint entrance set $V^+$ and exit set $V^-$, integer lower and upper capacities $\underline c,\bar c:A\to\mathbb Z$, and a finite nonempty $B^+\subseteq\mathbb Z^{V^+}$. A flow $\varphi:A\to\mathbb Z$ is feasible if $\underline c\le\varphi\le\bar c$, $\partial\varphi(v)=0$ at every vertex outside $V^+\cup V^-$, and $(\partial\varphi)^+\in B^+$, where $\partial\varphi(v)$ is out-flow minus in-flow at $v$ (7.1)–(7.4). Assume that a feasible flow exists, and let
--   $$\tilde B=\{(\partial\varphi)^-\mid\varphi\ \text{feasible flow}\}\subseteq\mathbb Z^{V^-}.\tag{7.5}$$
--   If $B^+$ satisfies (B1), then $\tilde B$ satisfies (B1):
--   for $x,y\in\tilde B$ and $u\in\operatorname{supp}^+(x-y)$ there is $v\in\operatorname{supp}^-(x-y)$ with $x-\chi_u+\chi_v\in\tilde B$.
--
--   The lemma says that the integral base sets are transformed into integral base sets through a network; it supplies the domain of the induced function of Theorem 7.2.
--
--   **Formalization Note.** (B1) together with finiteness and nonemptiness is the published `IsIntegralBaseSet`; $\tilde B$ is nonempty because a feasible flow exists. The entrance and exit sets may be empty. Parallel arcs and loops are allowed.
--
--   Differences from the source:
--   - reading: a (directed) graph G = (V, A; V⁺, V⁻) → finite arc type with tail/head maps; parallel arcs and loops allowed; reason: the page places no simplicity condition on G; a loop contributes zero to the boundary and parallel arcs are independent arcs
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 305, Lemma 7.1 (with the setting (7.1)–(7.5) on pp. 304–305)

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Supplement_Network

namespace SteinitzExchange.Duality.Supplement

/-- Murota 1996, p. 305, Lemma 7.1. Let `G = (N, A; V⁺, V⁻)` be a directed graph with disjoint
entrance and exit sets, integer lower and upper capacities `c̲, c̄ : A → ℤ`, and a finite nonempty
`B⁺ ⊆ ℤ^{V⁺}`, and assume that a feasible flow exists. If `B⁺` satisfies (B1), then
`B̃ = {(∂φ)⁻ | φ feasible flow}` of (7.5) satisfies (B1). -/
theorem network_base {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A]
    (tail head : A → N) (Vp Vm : Finset N) (hdisj : Disjoint Vp Vm) (lo up : A → ℤ)
    (Bp : Finset (Vp → ℤ)) (hBp : IsIntegralBaseSet Bp)
    (hfeas : (feasibleFlows tail head Vp Vm lo up Bp).Nonempty) :
    IsIntegralBaseSet (inducedBase tail head Vp Vm lo up Bp) := by sorry

end SteinitzExchange.Duality.Supplement
