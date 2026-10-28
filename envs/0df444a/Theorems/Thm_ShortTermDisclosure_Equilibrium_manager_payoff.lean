-- Prove2me | Theorems.Thm_ShortTermDisclosure_Equilibrium_manager_payoff
-- name    : ShortTermDisclosure.Equilibrium.manager_payoff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:01.550372+00:00
-- url     : https://prove2.me/theorems/da12157b-b589-4514-b368-669fbf54cba5
-- title:
--   Equations (7)–(8) — expected manager payoff
-- statement:
--   Let the shareholder intervene when her uniformly distributed alternative value $\mu$ exceeds a threshold $t\in[0,\bar\mu]$. The informed manager with current value $v$ then receives expected liquidation value
--
--   $$E[V\mid v,t]=\left(1-\frac{t}{\bar\mu}\right)E[\mu\mid\mu\ge t]+\frac{t}{\bar\mu}v.$$
--
--   For $t<\bar\mu$, the conditional mean is $(t+\bar\mu)/2$. Using the threshold after disclosure or silence gives (7) or (8). **Formalization Note** The zero-probability event at $t=\bar\mu$ is assigned its limiting mean, whose coefficient is zero.
-- source:
--   Jia & Menon, Shareholder short-termism, corporate control and voluntary disclosure, authors' manuscript (SSRN 4029096, Minerva Access copy), p. 15 (PDF 18), (7)–(8)

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model

namespace ShortTermDisclosure.Equilibrium

theorem manager_payoff (muhi t v : ℝ) (hm : 0 < muhi)
    (ht0 : 0 ≤ t) (ht1 : t ≤ muhi) :
    managerValue muhi t v =
      (1 - t / muhi) * condMeanAbove muhi t + (t / muhi) * v ∧
    (t < muhi → condMeanAbove muhi t = (t + muhi) / 2) := by sorry

end ShortTermDisclosure.Equilibrium
