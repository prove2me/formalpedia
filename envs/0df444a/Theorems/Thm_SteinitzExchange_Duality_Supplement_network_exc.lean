-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_Supplement_network_exc
-- name    : SteinitzExchange.Duality.Supplement.network_exc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:30:49.30566+00:00
-- url     : https://prove2.me/theorems/f6b85391-dc10-4071-9b7c-753821c0caf1
-- title:
--   Theorem 7.2 — an M-concave function induced through a network is M-concave
-- statement:
--   Let $G=(V,A;V^+,V^-)$ be a finite directed graph with disjoint entrance set $V^+$ and exit set $V^-$, integer lower and upper capacities $\underline c,\bar c:A\to\mathbb Z$, real arc weights $w:A\to\mathbb R$, a finite nonempty $B^+\subseteq\mathbb Z^{V^+}$ and $\omega^+:B^+\to\mathbb R$. Feasible flows are as in (7.2)–(7.4), and a feasible flow is assumed to exist. Let $\tilde B=\{(\partial\varphi)^-\mid\varphi\ \text{feasible}\}$ and
--   $$\tilde\omega(x)=\max\{\langle w,\varphi\rangle_A+\omega^+((\partial\varphi)^+)\mid\varphi\ \text{feasible flow with}\ (\partial\varphi)^-=x\}\qquad(x\in\tilde B),\tag{7.6}$$
--   where $\langle w,\varphi\rangle_A=\sum_{a\in A}w(a)\varphi(a)$. If $\omega^+$ satisfies (EXC), then $\tilde\omega$ satisfies (EXC) on $\tilde B$.
--
--   This is the main result of Section 7: M-concave functions are transformed into M-concave functions through a network, extending the classical induction of matroids through bipartite graphs. Theorems 7.3–7.5 and the convolution theorem (Theorem 6.10) are special cases.
--
--   **Formalization Note.** (EXC) is the published `SatisfiesEXC`; `inducedBase` and `inducedValue` are $\tilde B$ and $\tilde\omega$. The exit domain is $(\partial\varphi)^-$ itself (out-flow minus in-flow at each exit), not its negative. The entrance and exit sets may be empty.
--
--   Differences from the source:
--   - reading: a (directed) graph G = (V, A; V⁺, V⁻) → finite arc type with tail/head maps; parallel arcs and loops allowed; reason: the page places no simplicity condition on G; a loop contributes zero to the boundary and parallel arcs are independent arcs
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 305, Theorem 7.2 (with the setting (7.1)–(7.6) on pp. 304–305)

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Exchange
import Definitions.Def_SteinitzExchange_Duality_Supplement_Network

namespace SteinitzExchange.Duality.Supplement

/-- Murota 1996, p. 305, Theorem 7.2. Let `G = (N, A; V⁺, V⁻)` be a directed graph with disjoint
entrance and exit sets, integer capacities `c̲, c̄ : A → ℤ`, real arc weights `w : A → ℝ`, a finite
nonempty `B⁺ ⊆ ℤ^{V⁺}` and `ω⁺ : B⁺ → ℝ`, and assume that a feasible flow exists. If `ω⁺`
satisfies (EXC), then `ω̃ : B̃ → ℝ` of (7.6),
`ω̃(x) = max{⟨w, φ⟩_A + ω⁺((∂φ)⁺) | φ feasible flow with (∂φ)⁻ = x}`, satisfies (EXC). -/
theorem network_exc {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A]
    (tail head : A → N) (Vp Vm : Finset N) (hdisj : Disjoint Vp Vm) (lo up : A → ℤ)
    (w : A → ℝ) (Bp : Finset (Vp → ℤ)) (hBp : Bp.Nonempty) (ωp : (Vp → ℤ) → ℝ)
    (hωp : SatisfiesEXC Bp ωp)
    (hfeas : (feasibleFlows tail head Vp Vm lo up Bp).Nonempty) :
    SatisfiesEXC (inducedBase tail head Vp Vm lo up Bp)
      (inducedValue tail head Vp Vm lo up w Bp ωp) := by sorry

end SteinitzExchange.Duality.Supplement
