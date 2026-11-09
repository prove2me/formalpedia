-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_poissonization_reduction
-- name    : QuadraticProbe717.Insertion.poissonization_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:45.010351+00:00
-- url     : https://prove2.me/theorems/8561c3dc-62c8-41dd-b43e-8098455f2db0
-- title:
--   Lemma 3.1 — Poissonization reduction
-- statement:
--   Let $n>0$, fix a completion order, and let $m$ be any positive integer. Let $T_m$ be the next insertion cost after $m$ independent uniform hashes. Independently sample $N\sim\operatorname{Poisson}(m)$ and then the $N+1$ hashes defining $T_N$. For every integer $k\ge0$,
--   $$\Pr[T_m>k]\le2\Pr[T_N>k].$$
--   The statement includes $m\ge n$ and the positive-probability event $N\ge n$, using the prescribed cost $2n$ for every insertion into a full table.
--
--   Differences from the source:
--   - encoding: distinct keys with independent uniform hashes and arbitrary fixed offset completion → insertion-time indices, ZMod n slots, every fixed completion permutation, and exact finite averages; reason: key labels do not affect insertion; repeated quadratic probes and the first empty slot are retained
--   - encoding: random insertion count N with mean m → integration of the conditional fixed-load tails against Poisson(m); reason: the same mixture law, with no conditioning on N<n
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Lemma 3.1, equation (1), p. 6 (PDF p. 6)

import Definitions.Def_QuadraticProbe717_Insertion_laws

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem poissonization_reduction (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n))
    (m : ℕ) (hm : 0 < m) (k : ℕ) :
    fixedTail n m π k ≤ 2 * poissonTail n π (m : ℝ≥0) k := by sorry

end QuadraticProbe717.Insertion
