-- Prove2me | Theorems.Thm_TsayQF_EffQF_qf_purchase
-- name    : TsayQF.EffQF.qf_purchase
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:42.489155+00:00
-- url     : https://prove2.me/theorems/810015e7-3f1c-475e-9b79-3a75de6df557
-- title:
--   §6.1, p. 1347 (σ_ε = 0) — the retailer's unique optimal purchase in [q(1 − ω), Q] is μ ⊥ [q(1 − ω), Q]
-- statement:
--   Let $p > m > 0$, $u < m$, $s \ge 0$ be the cost data and let the transfer price satisfy $u < c < p+s$. With $\sigma_\varepsilon=0$, a retailer that observes the signal $\mu$ and buys $r$ units earns
--   $$G(r\mid\mu) = p\min[\mu,r] - c\,r - s[\mu-r]^+ + u[r-\mu]^+ .$$
--   For every $\mu$ and every interval $[a,b]$ with $a \le b$, a purchase $r \in [a,b]$ maximizes $G(\cdot\mid\mu)$ over $[a,b]$ if and only if
--   $$r = \mu \perp [a,b] = \max\{a,\min\{\mu,b\}\},$$
--   the point of $[a,b]$ closest to $\mu$.
--
--   Applied with $a = q(1-\omega)$ (the minimum purchase) and $b = Q$ (the EM's production), this is the QF purchase rule $r^*_{QF}(q,Q,\mu) = \mu \perp [q(1-\omega),Q]$ that both firms anticipate.
--
--   **Formalization Note.** The page prints the rule with the target $\mu + z_\varepsilon\sigma_\varepsilon$; at $\sigma_\varepsilon = 0$ the target is $\mu$. The paper's standing assumption is $m < c < p$; the statement assumes only $u < c < p+s$, a generalization needed because the mission applies the rule at $c = \bar c(\psi)$, which can exceed $p$ when $s > 0$.
-- source:
--   Tsay, The quantity flexibility contract and supplier-customer incentives, Management Science 45(10) (1999), p. 1347, §6.1 and footnote 7 (instance σ_ε = 0)

import Mathlib
import Definitions.Def_TsayQF_EffQF_Model

open MeasureTheory ProbabilityTheory

namespace TsayQF.EffQF

/-- §6.1, p. 1347, at `σ_ε = 0`: given the signal `μ`, the retailer's unique optimal purchase in
`[a, b]` is `μ ⊥ [a, b]`. -/
theorem qf_purchase (D : Data) (c : ℝ) (hcu : D.u < c) (hcp : c < D.p + D.s) :
    ∀ μ a b r, a ≤ b → r ∈ Set.Icc a b →
      (IsMaxOn (fun r' => G D c r' μ) (Set.Icc a b) r ↔ r = clip μ a b) := by sorry

end TsayQF.EffQF
