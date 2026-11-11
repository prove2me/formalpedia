-- Prove2me | Theorems.Thm_OrderedSearchExact_Exact_proposition_4_9
-- name    : OrderedSearchExact.Exact.proposition_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:57.444483+00:00
-- url     : https://prove2.me/theorems/a0eb6a52-b2a4-4b75-ac8a-290c963cd760
-- title:
--   Proposition 4.9 — near-pi compact mixtures
-- statement:
--   There are positive widths $W_m\to\infty$, positive shifts $d_m\uparrow\pi$ from below, and uniform margins $0<\rho_m<1$ such that the specific quartic density $h_{W_m}$ is a compactly supported probability density and satisfies
--
--   $$|b_{h_{W_m}}(x)-b_{h_{W_m}}(x-d_m)|\le2\rho_m\sqrt{a_{h_{W_m}}(x)a_{h_{W_m}}(x-d_m)}\qquad(m\in\mathbb N,\ x\in\mathbb R).$$
--
--   Every sequence is chosen before $x$; the margin is uniform on the entire real line. This provides the compact packet parameters for the asymptotic construction.
--
--   Differences from the source:
--   - encoding: sequences W_m tending to infinity, d_m increasing to pi, and rho_m<1 for h_Wm → Tendsto W atTop atTop, Monotone d, convergence to pi with 0<d_m<pi, 0<rho_m<1, and the explicit density predicate; reason: the widths and shifts have their construction domains; a positive strict margin is available from the proof, and no point-dependent margin is substituted
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), Proposition 4.9, p.21 (PDF p.21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Parameters

namespace OrderedSearchExact.Exact

theorem proposition_4_9 :
    ∃ W d ρ : ℕ → ℝ, NearPi W d ρ := by sorry

end OrderedSearchExact.Exact
