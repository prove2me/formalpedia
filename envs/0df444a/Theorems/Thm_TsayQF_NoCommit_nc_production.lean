-- Prove2me | Theorems.Thm_TsayQF_NoCommit_nc_production
-- name    : TsayQF.NoCommit.nc_production
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:27.476981+00:00
-- url     : https://prove2.me/theorems/ed43feac-2a3a-4d3d-b472-9d1ab6c8c785
-- title:
--   §5.2, p. 1347 — the EM's optimal production without commitment is Q*_NC = Θ^{-1}((c − m)/(c − u)) + z_εσ_ε
-- statement:
--   In the supply chain of Tsay (1999) with costs $p > c > m > 0$, $u < m$, $s \ge 0$, let the signal $\mu$ have a differentiable, strictly increasing distribution function $\Theta$ and finite variance, let $\sigma_\varepsilon \ge 0$, and let $z_\varepsilon = \Phi^{-1}\big((p+s-c)/(p+s-u)\big)$. Without commitment the retailer buys $r^*_{NC}(Q,\mu) = \min[\mu + z_\varepsilon\sigma_\varepsilon, Q]$, so the EM producing $Q$ expects
--   $$\pi_{EM,NC}(Q) = (c-u)\,E_\mu\min[\mu + z_\varepsilon\sigma_\varepsilon, Q] - (m-u)\,Q .$$
--   Then some $Q$ solves
--   $$\Theta(Q - z_\varepsilon\sigma_\varepsilon) = \frac{c-m}{c-u},$$
--   and $Q$ maximizes $\pi_{EM,NC}$ over $\mathbb R$ if and only if it solves this equation; that is, $Q^*_{NC} = \Theta^{-1}\big((c-m)/(c-u)\big) + z_\varepsilon\sigma_\varepsilon$.
--
--   The EM is a newsvendor with underage cost $c-m$ and overage cost $m-u$ facing the retailer's purchase rather than market demand.
--
--   **Formalization Note** $\Theta^{-1}$ and $\Phi^{-1}$ enter through their defining equations ($\Phi(z) = (p+s-c)/(p+s-u)$ as a hypothesis on a real $z$). Productions range over all of $\mathbb R$.
-- source:
--   Tsay, The quantity flexibility contract and supplier-customer incentives, Management Science 45(10) (1999), p. 1347, §5.2

import Mathlib
import Definitions.Def_TsayQF_NoCommit_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TsayQF.NoCommit

theorem nc_production (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (hΘd : Differentiable ℝ (cdf ν)) (hν : MemLp id 2 ν)
    (v : ℝ≥0) (z : ℝ) (hz : cdf (gaussianReal 0 1) z = kR D) :
    (∃ Q : ℝ, cdf ν (Q - z * Real.sqrt v) = kEM D) ∧
      ∀ Q : ℝ, IsMaxOn (emProfit D ν v z) Set.univ Q ↔
        cdf ν (Q - z * Real.sqrt v) = kEM D := by sorry

end TsayQF.NoCommit
