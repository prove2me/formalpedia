-- Prove2me | Theorems.Thm_PerishablePricing_Backlog_theorem_1
-- name    : PerishablePricing.Backlog.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:14.520161+00:00
-- url     : https://prove2.me/theorems/4e5396fe-5e1d-481c-baa6-9579e5e9dec0
-- title:
--   Theorem 1, p. 291 — L♮-concavity of the profit-to-go and monotone, bounded-sensitivity optimal policy (backlogging)
-- statement:
--   Consider the backlogging perishable inventory–pricing model under the standing assumptions of §3 and the assumption $c \le h^-/(1-\gamma)$ of §4. For $t = 1, \dots, T + 1$:
--
--   1. $f_t(s)$, $g_t(s, s_l, d \mid \varepsilon)$ and $\phi_t(s, s_l, d, a \mid \varepsilon)$ are L♮-concave in $s$, $(s, s_l, d)$ and $(s, s_l, d, a)$ on $\mathcal{V}_{l-1,l-1}$, $\mathcal{V}_{l+1,l}$ and $\mathcal{V}_{l+2,l}$ respectively, for every noise value $\varepsilon$.
--   2. The optimal order-up-to level $s_{lt}(s)$ and the optimal demand level $d_t(s)$ are nondecreasing in $s$, so the optimal price $p_t(s) = P(d_t(s))$ is nonincreasing in $s$.
--   3. For every $\omega \ge 0$,
--   $$s_{lt}(s + \omega e) \le s_{lt}(s) + \omega \quad\text{and}\quad d_t(s + \omega e) \le d_t(s) + \omega. \tag{7}$$
--   4. Given the realized demand, the optimal depletion $a_t(s, s_l, d \mid \varepsilon)$ is nondecreasing in $(s, s_l, d)$, and for every $\omega \ge 0$
--   $$a_t(s + \omega e, s_l + \omega, d + \omega \mid \varepsilon) \le a_t(s, s_l, d \mid \varepsilon) + \omega. \tag{8}$$
--
--   Here $s_{lt}(s)$, $d_t(s)$ and $a_t$ are the largest optimal decisions. The theorem says that fresher inventory leads to ordering less and charging more, that one more unit of inventory of any age raises the order-up-to level and the demand level by at most one unit, and that the depletion responds monotonically and with bounded sensitivity.
--
--   **Formalization Note** Real case only ($\mathbb{F} = \mathbb{R}$). Time is counted in periods to go: part 1 for $f$ holds for every `f n` (including $f_{T+1} = 0$); the parts on $g$, $\phi$ and the decisions concern the periods $t \le T$, with continuation `f n` and value `f (n+1)`. The largest optimal decisions are hypotheses at the points compared, which is the paper's "the existence of optimal solutions is straightforward to check": a global selector would make the statement vacuous where no largest optimum exists (at $\gamma = 1$ and $k \ge 1$, $G_T$ does not depend on $s_l$). In (7) only the state is shifted; in (8) the shift acts on $(s, s_l, d)$ jointly with $\varepsilon$ fixed, and both compared points have $s_1 \le \dots \le s_l$. In the depletion parts $d$ and $\varepsilon$ are arbitrary reals, as on the page. The §4 assumption is the hypothesis $(1-\gamma)c \le h^-$, the faithful reading also at $\gamma = 1$.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, Theorem 1, eqs. (7)–(8), p. 291 (PDF p. 9)

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_Model

namespace PerishablePricing.Backlog

/-- Theorem 1 (Monotonicity Properties of Backlog Model), p. 291. Under the standing assumptions
of §3 and §4 (`(1 − γ)c ≤ h⁻`), for every number of periods to go:
1. `f_t` is L♮-concave on `𝒮`; `g_t(· | ε)` on `𝒱_{l+1,l}` and `φ_t(· | ε)` on `𝒱_{l+2,l}`;
2. the largest optimal order-up-to level `s_{lt}(s)` and demand level `d_t(s)` are nondecreasing
   in `s ∈ 𝒮`, and the price `P(d_t(s))` is nonincreasing;
3. (7): `s_{lt}(s + ωe) ≤ s_{lt}(s) + ω` and `d_t(s + ωe) ≤ d_t(s) + ω` for `ω ≥ 0`;
4. the largest optimal depletion `a_t(s, s_l, d | ε)` is nondecreasing in `(s, s_l, d)`, and (8):
   `a_t(s + ωe, s_l + ω, d + ω | ε) ≤ a_t(s, s_l, d | ε) + ω` for `ω ≥ 0`.
Largest optimal decisions are hypotheses at the points compared (the paper's existence claim). -/
theorem theorem_1 {L k : ℕ} (M : Model L k) (hc : (1 - M.γ) * M.c ≤ M.hm) :
    (∀ n : ℕ, LNatConcaveOn (V L L) (M.f n)) ∧
    (∀ (n : ℕ) (ε : ℝ), LNatConcaveOn (V (L + 2) (L + 1)) (M.gJoint n ε)) ∧
    (∀ (n : ℕ) (ε : ℝ), LNatConcaveOn (V (L + 3) (L + 1)) (M.phiJoint n ε)) ∧
    (∀ (n : ℕ) (s s' : Fin L → ℝ) (S D S' D' : ℝ),
      s ∈ Model.StateSpace L → s' ∈ Model.StateSpace L → s ≤ s' →
      M.IsLargestOptOrder n s S D → M.IsLargestOptOrder n s' S' D' →
      S ≤ S' ∧ D ≤ D' ∧ M.P D' ≤ M.P D) ∧
    (∀ (n : ℕ) (s : Fin L → ℝ) (ω S D S' D' : ℝ),
      s ∈ Model.StateSpace L → 0 ≤ ω →
      M.IsLargestOptOrder n s S D → M.IsLargestOptOrder n (s + ω • (1 : Fin L → ℝ)) S' D' →
      S' ≤ S + ω ∧ D' ≤ D + ω) ∧
    (∀ (n : ℕ) (ε : ℝ) (s s' : Fin L → ℝ) (sl sl' d d' a a' : ℝ),
      s ∈ Model.StateSpace L → M.sLast s ≤ sl →
      s' ∈ Model.StateSpace L → M.sLast s' ≤ sl' →
      s ≤ s' → sl ≤ sl' → d ≤ d' →
      M.IsLargestOptDepletion n s sl d ε a → M.IsLargestOptDepletion n s' sl' d' ε a' →
      a ≤ a') ∧
    (∀ (n : ℕ) (ε : ℝ) (s : Fin L → ℝ) (sl d ω a a' : ℝ),
      s ∈ Model.StateSpace L → M.sLast s ≤ sl → 0 ≤ ω →
      M.IsLargestOptDepletion n s sl d ε a →
      M.IsLargestOptDepletion n (s + ω • (1 : Fin L → ℝ)) (sl + ω) (d + ω) ε a' →
      a' ≤ a + ω) := by sorry

end PerishablePricing.Backlog
