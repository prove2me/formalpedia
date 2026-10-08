-- Prove2me | Theorems.Thm_SethiChengSS_Finite_dp_ge_f_and_z_coercive
-- name    : SethiChengSS.Finite.dp_ge_f_and_z_coercive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:23.697065+00:00
-- url     : https://prove2.me/theorems/0c7b05a2-662c-4c1c-ab28-ed4f565ca550
-- title:
--   Proof of Theorem 4.1, p. 935, after (4.11) — v_n ≥ f_n, and z_n(i, ·) is coercive at +∞ and uniformly continuous
-- statement:
--   Consider the Markov-modulated inventory model of Sethi and Cheng under the standing assumptions of §2 and assumption (4.2). Let $v_n$ be the functions of the dynamic programming equations (3.2), and let
--   $$z_n(i,y) = c^i_n y + F_{n+1}(v_{n+1})(i,y). \qquad (4.11)$$
--   Then for every $n \in \langle 0, N-1\rangle$ and every demand state $i$:
--   1. $v_n(i,x) \ge f_n(i,x)$ for all $x$;
--   2. $z_n(i,y) \to +\infty$ as $y \to \infty$;
--   3. $z_n(i,\cdot)$ is uniformly continuous.
--
--   These are the hypotheses of Proposition 4.2 on $g = z_n(i,\cdot)$ other than $K$-convexity.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 935, proof of Theorem 4.1, after (4.11)

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Finite_KConvexity
import Definitions.Def_SethiChengSS_Finite_Model
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SethiChengSS.Finite

/-- Proof of Theorem 4.1 (Sethi–Cheng 1997, p. 935, after (4.11)): for `n ∈ ⟨0, N − 1⟩` and every
`i`, `v_n(i, x) ≥ f_n(i, x)`, and under (4.2) the function `z_n(i, y) = c^i_n y +
F_{n+1}(v_{n+1})(i, y)` tends to `+∞` as `y → ∞` and is uniformly continuous. -/
theorem dp_ge_f_and_z_coercive {L : ℕ} (D : Data L) (N : ℕ) (hS : Standing D)
    (h42 : Cond42 D N) :
    ∀ n < N, ∀ i, (∀ x, D.f n i x ≤ dpV D N n i x) ∧
      Tendsto (zFun D N n i) atTop atTop ∧ UniformContinuous (zFun D N n i) := by sorry

end SethiChengSS.Finite
