-- Prove2me | Theorems.Thm_PerishablePricing_Bounds_theorem_1_concavity
-- name    : PerishablePricing.Bounds.theorem_1_concavity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T21:16:08.875656+00:00
-- url     : https://prove2.me/theorems/d90b830f-499b-44e0-82a2-d93a027b0d85
-- title:
--   Theorem 1, p. 291, first sentence (k = 0) — f_t, g_t, φ_t are L♮-concave
-- statement:
--   Consider the backlogging model with lifetime $l\ge 2$ and zero lead time, under the standing assumptions of §3 and the assumption $c\le h^-/(1-\gamma)$ of §4. For every period:
--
--   1. the profit-to-go $f_t(s)$ is L♮-concave in $s$ on $\mathcal S=\mathcal V_{l-1,l-1}$;
--   2. for every noise value $\varepsilon$, $g_t(s,s_l,d\mid\varepsilon)$ is L♮-concave in $(s,s_l,d)$ on $\mathcal V_{l+1,l}=\{s_1\le\dots\le s_{l-1}\le s_l\}\times\mathbb R$;
--   3. for every noise value $\varepsilon$, $\varphi_t(s,s_l,d,a\mid\varepsilon)$ is L♮-concave in $(s,s_l,d,a)$ on $\mathcal V_{l+2,l}$.
--
--   This is the structural core of the analysis: concavity of $G_t(s,\cdot,d)$ in the order-up-to level, used to compare the optimal order with the myopic bounds, comes from it.
--
--   **Formalization Note.** Points of $\mathcal V_{l+1,l}$ are `w : Fin (L+2) → ℝ` read as $(s_1,\dots,s_{l-1},s_l,d)$, and points of $\mathcal V_{l+2,l}$ are `w : Fin (L+3) → ℝ` read as $(s_1,\dots,s_l,d,a)$; $d$ and $a$ are unconstrained reals, as on the page, and the shift by $\alpha e$ acts on all coordinates. Part 1 holds for every number of periods to go ($t=1,\dots,T+1$); parts 2 and 3 use the continuation `f n` ($t\le T$). The paper states Theorem 1 for any lead time $k<l$; this mission needs the case $k=0$ only. The carrier is $\mathbb R$.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, Theorem 1 (first sentence), p. 291, with lead time k = 0

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex
import Definitions.Def_PerishablePricing_Bounds_Model

namespace PerishablePricing.Bounds

/-- Theorem 1 (p. 291), first sentence, at lead time `k = 0`: for every number of periods to go,
`f_t(s)` is L♮-concave on `𝒮 = 𝒱_{l−1,l−1}`, and, for every noise value `ε`,
`g_t(s, s_l, d | ε)` is L♮-concave in `(s, s_l, d)` on `𝒱_{l+1,l}` and
`φ_t(s, s_l, d, a | ε)` is L♮-concave in `(s, s_l, d, a)` on `𝒱_{l+2,l}`.
A point of `𝒱_{l+1,l}` is `w : Fin (L+2) → ℝ` read as `(s₁, …, s_{l−1}, s_l, d)`, and a point of
`𝒱_{l+2,l}` is `w : Fin (L+3) → ℝ` read as `(s₁, …, s_{l−1}, s_l, d, a)`. -/
theorem theorem_1_concavity (M : Model) (hM : M.Standing) (L : ℕ) (hL : 1 ≤ L)
    (hback : (1 - M.γ) * M.c ≤ M.hm) (n : ℕ) :
    PerishablePricing.Backlog.LNatConcaveOn (stateSpace L) (M.f n) ∧
    (∀ ε : ℝ, PerishablePricing.Backlog.LNatConcaveOn (PerishablePricing.Backlog.V (L + 2) (L + 1)) (fun w : Fin (L + 2) → ℝ =>
      M.g (M.f n) (Fin.init (Fin.init w)) (Fin.init w (Fin.last L)) (w (Fin.last (L + 1))) ε)) ∧
    (∀ ε : ℝ, PerishablePricing.Backlog.LNatConcaveOn (PerishablePricing.Backlog.V (L + 3) (L + 1)) (fun w : Fin (L + 3) → ℝ =>
      M.phi (M.f n) (Fin.init (Fin.init (Fin.init w))) (Fin.init (Fin.init w) (Fin.last L))
        (Fin.init w (Fin.last (L + 1))) (w (Fin.last (L + 2))) ε)) := by sorry

end PerishablePricing.Bounds
