-- Prove2me | Theorems.Thm_RelQueryPTime_tuple_arith
-- name    : RelQueryPTime.tuple_arith
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:40:11.726278+00:00
-- url     : https://prove2.me/theorems/468a0ea1-dec0-4227-8758-83aa288f1a17
-- title:
--   Proof of Theorem 1 — arithmetic on $k$-tuples is first order with $\le$
-- statement:
--   Fix a scheme $\sigma$ and $k \ge 0$, and read a $k$-tuple $\bar s$ over $\{0,\dots,n-1\}$ as the base-$n$ number $\mathrm{value}(\bar s)$, first coordinate most significant. There are first-order formulas of relational calculus with $\le$, correct on every ordered database with any number $n$ of elements, that define:
--
--   1. $\mathrm{value}(\bar s) = 0$;
--   2. $\mathrm{value}(\bar s) = n^k - 1$;
--   3. $\mathrm{value}(\bar t) = \mathrm{value}(\bar s) + 1$;
--   4. $\mathrm{value}(\bar t) = \mathrm{value}(\bar s) + n^b$, for each $b < k$.
--
--   The proof of Theorem 1 uses these to name time steps and tape cells by $k$-tuples of variables ($t = 0$, $t - 1$, $p \pm 1$, time $n^k - 1$) and to locate the bit tables of the input.
--
--   **Formalization Note** In 1–2 the free variables $x_0,\dots,x_{k-1}$ hold $\bar s$; in 3–4 the free variables $x_0,\dots,x_{2k-1}$ hold $\bar s$ and then $\bar t$. Clause 2 is written $\mathrm{value}(\bar s) + 1 = n^k$.
--
--   Differences from the source:
--   - reading: k-tuples of variables denote numbers between 0 and n^k−1 → first-order definability of value = 0, value = n^k − 1, value + 1 and value + n^b (b < k) on k-tuples read in base n, first coordinate most significant; reason: the proof uses exactly these relations (t=0, t−1, p±1, n^k−1, the table offsets) without stating them
--   - encoding: value = n^k − 1 → value + 1 = n^k; reason: avoids natural-number subtraction; the same relation, since n^k ≥ 1 whenever a k-tuple exists
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, proof of Theorem 1, p.149 ("We can use k-tuples of variables to denote numbers between 0 and n^k-1.") (PDF p.3)

import Mathlib
import Definitions.Def_RelQueryPTime_Syntax
import Definitions.Def_RelQueryPTime_TupleValue

namespace RelQueryPTime

/-- Arithmetic on `k`-tuples is first order with `≤` (Immerman, *Relational Queries Computable in Polynomial Time*, STOC 1982, proof of Theorem 1, p.149: "We can use
k-tuples of variables to denote numbers between 0 and n^k-1"). Reading a `k`-tuple `s` over
`{0, …, n-1}` as the base-`n` number `tupleValue k s`, there are first-order formulas, correct on
every database with any number `n` of elements, defining
1. `value(s) = 0`;
2. `value(s) = n^k - 1` (written `value(s) + 1 = n^k`);
3. `value(t) = value(s) + 1`;
4. `value(t) = value(s) + n^b`, for each `b < k`.

**Formalization Note** In 1–2 the free variables are `0, …, k-1` (holding `s`); in 3–4 they are
`0, …, 2k-1`, holding `s` and then `t`. -/
theorem tuple_arith (σ : Schema) (k : ℕ) :
    (∃ φ : Formula σ, φ.IsFO ∧ φ.fv ⊆ {i | i < k} ∧
      ∀ (n : ℕ) (B : Database σ n) (s : Fin k → Fin n),
        φ.query k n B s ↔ tupleValue k s = 0) ∧
    (∃ φ : Formula σ, φ.IsFO ∧ φ.fv ⊆ {i | i < k} ∧
      ∀ (n : ℕ) (B : Database σ n) (s : Fin k → Fin n),
        φ.query k n B s ↔ tupleValue k s + 1 = n ^ k) ∧
    (∃ φ : Formula σ, φ.IsFO ∧ φ.fv ⊆ {i | i < k + k} ∧
      ∀ (n : ℕ) (B : Database σ n) (s t : Fin k → Fin n),
        φ.query (k + k) n B (Fin.append s t) ↔ tupleValue k t = tupleValue k s + 1) ∧
    ∀ b < k, ∃ φ : Formula σ, φ.IsFO ∧ φ.fv ⊆ {i | i < k + k} ∧
      ∀ (n : ℕ) (B : Database σ n) (s t : Fin k → Fin n),
        φ.query (k + k) n B (Fin.append s t) ↔ tupleValue k t = tupleValue k s + n ^ b := by sorry

end RelQueryPTime
