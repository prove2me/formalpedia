-- Prove2me | Theorems.Thm_PriceQualityService_Oligopoly_eq_EC_3
-- name    : PriceQualityService.Oligopoly.eq_EC_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:22.633958+00:00
-- url     : https://prove2.me/theorems/644ec94e-bbfc-4f47-899b-329ad7dffb1e
-- title:
--   (EC.3): equilibrium qualities and durations follow the monopoly rules
-- statement:
--   Assume $c_i > 0$ for every product. Let $(\mathbf p, \mathbf q, \mathbf t)$ be a Nash equilibrium of the joint price–quality–service competition, in which firm $i$ chooses $(p_i, q_i, t_i) \in \mathbb R \times \mathbb R \times [t_s, t_l]$ with payoff (6). Then for every firm $i$:
--
--   1. the quality is $q_i = \dfrac{\alpha_i + t_i b_i}{2 c_i}$;
--   2. the duration $t_i$ maximizes the duration index over $[t_s, t_l]$:
--   $$
--   \frac{b_i^2 t_i^2}{4c_i} + \Big(s_i - a_i + \frac{\alpha_i b_i}{2c_i}\Big) t_i \;\ge\; \frac{b_i^2 \tau^2}{4c_i} + \Big(s_i - a_i + \frac{\alpha_i b_i}{2c_i}\Big) \tau \qquad \text{for all } \tau \in [t_s, t_l].
--   $$
--
--   These are the rules by which the monopolist sets quality and duration, so competition leaves both decisions unchanged.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 2 (PDF p. 35), (EC.3)

import Mathlib
import Definitions.Def_PriceQualityService_Oligopoly_Model

namespace PriceQualityService.Oligopoly

/-- (EC.3), Online Supplement p. 2: in every Nash equilibrium of the joint price–quality–service
competition, each firm `i` sets its quality at `q_i = (α_i + t_i b_i)/(2 c_i)` and chooses a
service duration `t_i` that maximizes the duration index
`b_i² t²/(4 c_i) + (s_i − a_i + α_i b_i/(2 c_i)) t` over `[t_s, t_l]` — the same rules as in the
monopolistic problem. -/
theorem eq_EC_3 {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
    (x : Fin N → ℝ × ℝ × ℝ) (hx : IsOligopolyEquilibrium α a b c s ts tl x) (i : Fin N) :
    qualities x i = (α i + durations x i * b i) / (2 * c i) ∧
      ∀ τ ∈ Set.Icc ts tl, durationIndex α a b c s i τ ≤ durationIndex α a b c s i (durations x i) := by sorry

end PriceQualityService.Oligopoly
