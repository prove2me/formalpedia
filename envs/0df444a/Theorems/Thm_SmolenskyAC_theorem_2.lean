-- Prove2me | Theorems.Thm_SmolenskyAC_theorem_2
-- name    : SmolenskyAC.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:51:04.452512+00:00
-- url     : https://prove2.me/theorems/ff544686-38c1-4bb4-9ff3-c185dd9661d1
-- title:
--   Theorem 2 — depth-$k$ circuits with AND, OR, NOT, $\mathrm{MOD}_p$ need $\exp(\Omega(n^{1/2k}))$ AND/OR gates for $\mathrm{MOD}_r$, $r$ not a power of $p$
-- statement:
--   Let $p$ be a prime, $r\ge1$ an integer that is not a power $p^m$ ($m\ge0$) of $p$, and $k\ge1$. Then there are $c>0$ and $N$ such that for every $n\ge N$, every circuit on $n$ inputs with basic operations AND, OR, NOT and $\mathrm{MOD}_p$ of unbounded fan-in, of depth at most $k$, whose output equals $\mathrm{MOD}_r(x_1,\dots,x_n)$ on every assignment, has at least
--
--   $$\exp\big(c\, n^{1/(2k)}\big)$$
--
--   AND and OR gates. NOT and $\mathrm{MOD}_p$ gates are not counted.
--
--   This is the paper's main result: constant-depth circuits with modular counting gates for one prime cannot count modulo a number that is not a power of that prime. It contains Yao's PARITY bound and, with $\mathrm{MOD}_q$ reducible to MAJORITY, Razborov's MAJORITY bound.
--
--   **Formalization Note** The constants $c$ and $N$ depend only on $p$, $r$ and $k$. Constants may sit on wires without counting as gates.
--
--   Differences from the source:
--   - reading: requires exp(O(n^(1/2k))) AND and OR gates (as printed) → at least exp(c·n^(1/(2k))) gates for some c > 0 and all n ≥ N; reason: a requirement of at most exp(O(·)) gates says nothing; the abstract presents the result as a lower bound containing Yao's and Razborov's, so the O is Ω; the bound is for all large n (at n = 0 MOD_r is the constant 0)
--   - reading: r is not a power of p → ¬∃ m ≥ 0, r = p^m; reason: the abstract's r ≠ p^m; m = 0 excludes r = 1, for which MOD_1 is constant
--   - encoding: the modulus r → 0 < r; reason: modulus 0 is undefined
--   - encoding: the exponent 1/2k → 1/(2k) with k ≥ 1; reason: the printed stacked fraction; at k = 0 the exponent is undefined
--   - generalization: a depth k circuit → depth at most k; reason: a circuit of depth exactly k is one case
--   - generalization: a circuit is a transitively closed set whose only minimal elements are the inputs and whose maximal elements are the outputs (p.78) → gates listed in topological order, sources among inputs, Boolean constants and earlier gates; repeated wires, empty fan-in and gates feeding no output allowed; reason: the page's circuits are the special case without constants, repeats or dangling gates, and every gate of such a circuit is counted in both models
--   - generalization: NOT takes one input → a NOT gate may have any fan-in and negates its first source (true with none); reason: a page NOT gate is the fan-in 1 case; the extra sources are ignored, and they only increase the depth
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, Theorem 2, p.81 (pdf 5); abstract, p.77 (pdf 1)

import Mathlib
import Definitions.Def_SmolenskyAC_Circuit
import Definitions.Def_SmolenskyAC_GoalBasis

namespace SmolenskyAC

/-- **Theorem 2** (Smolensky, STOC 1987, p.81): let `p` be a prime number and `r` not a power of
`p`; then computing `MOD_r` by a depth `k` circuit with basic operations AND, OR, NOT and `MOD_p`
requires `exp(Ω(n^{1/2k}))` AND and OR gates.

For a prime `p`, an `r > 0` that is not `p^m` for any `m ≥ 0`, and `k ≥ 1`, there are `c > 0` and
`N` such that for every `n ≥ N`, every circuit on `n` inputs with gates AND, OR, NOT, `MOD_p` of
unbounded fan-in, of depth at most `k`, whose output is `MOD_r` on every assignment, has at least
`exp(c · n^{1/(2k)})` AND and OR gates.

**Formalization Note.** The scan prints `exp(O(n^{1/2k}))`; a lower bound "requires at most" says
nothing, and the abstract presents the result as a lower bound containing Yao's and Razborov's,
so it is read as `Ω`. NOT and `MOD_p` gates are free; constants may sit on wires; `c` and `N`
depend only on `p`, `r`, `k`. `r > 0` excludes the modulus `0`; `k ≥ 1` keeps `1/(2k)` defined. -/
theorem theorem_2 (p r k : ℕ) (hp : p.Prime) (hr : 0 < r) (hpow : ¬ ∃ m : ℕ, r = p ^ m)
    (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ C : Circuit GoalKind n Unit,
      C.depth ≤ k → (∀ x : Cube n, C.eval (goalOp p) x () = MODp r n x) →
      Real.exp (c * (n : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ)))) ≤ (C.countFlag goalFlag : ℝ) := by sorry

end SmolenskyAC
