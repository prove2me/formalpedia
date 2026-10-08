-- Prove2me | Theorems.Thm_TractableDRO_Unified_pi_le_piOf
-- name    : TractableDRO.Unified.pi_le_piOf
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:36.619877+00:00
-- url     : https://prove2.me/theorems/1c9f607b-6522-4cb8-9a96-fbec1eebc720
-- title:
--   Theorem 4, p. 911, (26) (right inequality) — the infimal convolution π(r⁰, r) is at most each π^s(r⁰, r)
-- statement:
--   Let the data $\mathcal V,\hat{\mathcal V},F,\Sigma,F_\sigma,g_\sigma,\hat{\mathcal W}_\sigma,\sigma_f,\sigma_b$ be arbitrary, let $\pi^1,\pi^2,\pi^3$ be the bounds (21), (22), (24) built from them, and let $S\subseteq\{1,2,3\}$. Define the unified bound by the infimal convolution
--   $$\pi(r^0,r)=\inf\Big\{\sum_{s\in S}\pi^s(r^{0,s},r^s):\ r^0=\sum_{s\in S}r^{0,s},\ r=\sum_{s\in S}r^s\Big\}.\quad(25)$$
--   Then for every $r^0\in\mathbb R$, $r\in\mathbb R^{N_E}$ and every $s\in S$,
--   $$\pi(r^0,r)\le\pi^s(r^0,r).$$
--
--   This is the right inequality of (26) in Theorem 4 of Goh and Sim: combining the bounds never does worse than any single one of them.
--
--   **Formalization Note** Values are in `EReal` (the printed "min" in (25) is read as an infimum), and $S$ is a `Finset (Fin 3)`, index $0,1,2$ standing for the paper's $1,2,3$. No hypothesis is needed for this inequality.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 911, Theorem 4, (25), (26) (right inequality)

import Mathlib
import Definitions.Def_TractableDRO_Unified_Model

open MeasureTheory ProbabilityTheory Matrix

namespace TractableDRO.Unified

/-- Theorem 4, p. 911, (26) (right inequality): `π(r⁰, r) ≤ π^s(r⁰, r)` for every `s ∈ S`. -/
theorem pi_le_piOf {n N Nσ : ℕ} (D : Data n N Nσ) (S : Finset (Fin 3)) (r0 : ℝ)
    (r : Fin n → ℝ) : ∀ s ∈ S, piU D S r0 r ≤ piOf D s r0 r := by sorry

end TractableDRO.Unified
