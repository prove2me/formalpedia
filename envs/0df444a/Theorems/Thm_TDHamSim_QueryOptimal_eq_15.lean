-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_eq_15
-- name    : TDHamSim.QueryOptimal.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:18:24.404288+00:00
-- url     : https://prove2.me/theorems/a66c6b53-42a7-4b2d-9c15-e609921308bc
-- title:
--   §4.1, eq. (15) — discretization error
-- statement:
--   Let $H$ satisfy (7) with $\alpha>0$, $\beta\ge0$ and $T>0$. For $J=2^m$, suppose $w=\alpha T/J\le1$, and form the ordered Cayley product $U_C$. Then
--
--   $$\|U_C-U_H(T)\|\le\frac{\beta T^2}{2J}+\frac{(\alpha T)^3}{12J^2}.$$
--
--   Both contributions and their exact constants are retained. This bound compares the discretized product with the ODE evolution, including noncommuting time-dependent Hamiltonians.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), §4.1, eq. (15) — discretization error, p.13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_Cayley

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- §4.1, eq. (15), p.13, with all standing assumptions of (7) and §4.1. -/
theorem eq_15 {n : ℕ} (m : ℕ) (H : ℝ → Mat (Bits n)) (α β T : ℝ)
    (hα : 0 < α) (hβ : 0 ≤ β) (hT : 0 < T) (hH : IsHamiltonian H α β T)
    (hw : stepWeight α T (2^m) ≤ 1) :
    opNorm (cayleyProduct H α T (2^m) - propagator H T T) ≤
      β*T^2/(2*(2^m : ℕ)) + (α*T)^3/(12*(2^m : ℕ)^2) := by sorry

end TDHamSim.QueryOptimal
