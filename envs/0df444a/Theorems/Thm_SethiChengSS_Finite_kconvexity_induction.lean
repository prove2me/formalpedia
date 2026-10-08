-- Prove2me | Theorems.Thm_SethiChengSS_Finite_kconvexity_induction
-- name    : SethiChengSS.Finite.kconvexity_induction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:28:29.250634+00:00
-- url     : https://prove2.me/theorems/25d5116e-ae1b-49b6-be01-cba760478d71
-- title:
--   Proof of Theorem 4.1, p. 935 — v_N is convex, and v_n(i, ·), z_n(i, ·) are K^i_n-convex for n ∈ ⟨0, N − 1⟩
-- statement:
--   Consider the Markov-modulated inventory model of Sethi and Cheng under the standing assumptions of §2, assumption (4.1), $K^i_n \ge \sum_j p_{ij}K^j_{n+1} \ge 0$, and assumption (4.2). Let $v_n$ be the functions of the dynamic programming equations (3.2) and $z_n(i,y) = c^i_n y + F_{n+1}(v_{n+1})(i,y)$ (4.11). Then:
--   1. $v_N(i,\cdot) = f_N(i,\cdot)$ is convex for every $i$;
--   2. for every $n \in \langle 0, N-1\rangle$ and every $i$, both $v_n(i,\cdot)$ and $z_n(i,\cdot)$ are $K^i_n$-convex:
--   $$K^i_n + z_n(i, y+a) \ge z_n(i,y) + a\,\frac{z_n(i,y) - z_n(i,y-b)}{b} \qquad (a \ge 0,\ b > 0),$$
--   and likewise for $v_n(i,\cdot)$.
--
--   $K$-convexity of $z_n(i,\cdot)$ is the structural property from which Proposition 4.2 produces the $(s,S)$ levels of period $n$.
--
--   **Formalization Note** The paper obtains $K$-convexity of $h_n$ from Proposition 4.2, whose hypothesis $g^* > -\infty$ (4.4) is never checked for $z_n$. $z_n(i,\cdot)$ can be unbounded below, for instance with a linear backlog cost $p$ and $c^i_n > p + c^j_{n+1}$. The statement here is the paper's conclusion, which still holds in that case, where $h_n = z_n$; a proof must cover it.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 935, proof of Theorem 4.1 (the induction)

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Finite_KConvexity
import Definitions.Def_SethiChengSS_Finite_Model
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SethiChengSS.Finite

/-- The `K`-convexity induction in the proof of Theorem 4.1 (Sethi–Cheng 1997, p. 935): under the
§2 assumptions, (4.1) and (4.2), `v_N(i, ·)` is convex, and for every `n ∈ ⟨0, N − 1⟩` and `i`
both `v_n(i, ·)` and `z_n(i, ·)` are `K^i_n`-convex. -/
theorem kconvexity_induction {L : ℕ} (D : Data L) (N : ℕ) (hS : Standing D)
    (h41 : Cond41 D N) (h42 : Cond42 D N) :
    (∀ i, ConvexOn ℝ Set.univ (dpV D N N i)) ∧
      ∀ n < N, ∀ i, BertsekasKConvex (D.K n i) (dpV D N n i) ∧
        BertsekasKConvex (D.K n i) (zFun D N n i) := by sorry

end SethiChengSS.Finite
