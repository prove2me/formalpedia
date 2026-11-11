-- Prove2me | Theorems.Thm_PrivateRoutingSignaling_PTAS_level_set_rounding
-- name    : PrivateRoutingSignaling.PTAS.level_set_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:52:07.222556+00:00
-- url     : https://prove2.me/theorems/e5de5f38-7d2b-4ba5-a12d-06ed93b2f7b8
-- title:
--   Lemma 3.3 — level-set rounding with exact cardinality and marginals
-- statement:
--   Let $P$ be all simple source-sink paths in a finite directed network, each containing at most $d$ arcs. Let $r_p\in[0,1]$ be arbitrary real numbers whose sum is a positive integer. There is a distribution $D$ on Boolean path vectors $S\in\{0,1\}^P$ such that
--
--   $$\sum_p S_p=\sum_p r_p\quad\text{for every supported }S,$$
--   $$\Pr_D[S_p=1]=r_p\quad(p\in P),$$
--   $$\left|\sum_{p\ni i}S_p-\sum_{p\ni i}r_p\right|\le2d\quad\text{for every arc }i\text{ and every supported }S.$$
--
--   The exact cardinality and marginal requirements coexist with simultaneous, absolute outcome-wise arc discrepancy. This is the level-set rounding statement used to obtain the uniform-flow rounding lemma. The distribution's weights and all prescribed marginals are real.
--
--   Differences from the source:
--   - encoding: paths, arcs, and Boolean outcomes in the finite network → Fin indices for graph-generated paths and Boolean function vectors, with finite real probability weights; reason: these enumerate exactly the source objects; positive weights characterize support and expectations of Boolean indicators equal event probabilities
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #439 (October 2026), Lemma 3.3, p. 12 (PDF p. 12), clauses 2–3 continuing on p. 13 (PDF p. 13); proof pp. 13–15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf

import Mathlib
import Definitions.Def_PrivateRoutingSignaling_PTAS_Network

set_option autoImplicit false
open scoped BigOperators

namespace PrivateRoutingSignaling.PTAS

/-- Lemma 3.3, pp.12–13, including exact cardinality, real marginals and absolute discrepancy. -/
theorem level_set_rounding (N : RoutingNetwork) (hN : NetworkValid N)
    (r : Path N → ℝ) (hr : ∀ p, r p ∈ Set.Icc (0 : ℝ) 1)
    (htotal : ∃ m : ℕ, 0 < m ∧ ∑ p, r p = (m : ℝ)) :
    ∃ w : (Path N → Bool) → ℝ, FiniteLaw w ∧
      (∀ S, 0 < w S → ∑ p, (if S p then (1 : ℝ) else 0) = ∑ p, r p) ∧
      (∀ p, ∑ S, w S * (if S p then (1 : ℝ) else 0) = r p) ∧
      ∀ S, 0 < w S → ∀ i : Fin N.arcs,
        |arcLoad N (fun p => if S p then 1 else 0) i - arcLoad N r i| ≤ 2 * (N.d : ℝ) := by sorry

end PrivateRoutingSignaling.PTAS
