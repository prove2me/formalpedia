-- Prove2me | Theorems.Thm_RadioInitBits_lemma_33_type1_collisions
-- name    : RadioInitBits.lemma_33_type1_collisions
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:10:50.175025+00:00
-- url     : https://prove2.me/theorems/42361fdc-5db7-4cf6-9083-2ab40d84e453
-- title:
--   Lemma 33 — in a type 1 phase at most $6f_{i-1}^2n/q_i$ nodes collide, except with probability $\le n^{-3}$
-- statement:
--   Let $n$ be the number of nodes. Consider a phase with $T$ bins, of relative length $q=T/n$, and a fraction $f$ for which the type 1 inequality of Definition 31 holds:
--   $$\frac{\left(\tfrac78 f\right)^2 n}{q}\ \ge\ \log_2 n .$$
--   Suppose $m\le fn$ participating nodes each choose one of the $T$ bins independently and uniformly at random. Then
--   $$\Pr\Big[\#\{\text{nodes that share their bin with another node}\}\ >\ \frac{6f^2n}{q}\Big]\ \le\ n^{-3}.$$
--
--   In phase $i>6$ of Algorithm 8, take $f=f_{i-1}$, $T=q_in$ and $m=F_{i-1}n$, the number of participating uninitialized nodes. Then this is Lemma 33: in a type 1 phase, at most $6f_{i-1}^2n/q_i$ uninitialized nodes collide, with high probability. Colliding nodes sleep through the next phases, and Lemma 34 and the proof of Theorem 5 use this bound to control how many nodes are asleep.
--
--   **Formalization Note** The probability is the fraction of the $T^m$ equally likely bin choices. The statement is for arbitrary $m\le fn$ and $T$; nothing else about Algorithm 8 enters.
--
--   Differences from the source:
--   - generalization: phase i > 6 of Algorithm 8, a type 1 phase, with F_{i−1}n participating uninitialized nodes → any m ≤ f n nodes choosing independently and uniformly among any T bins, under the type 1 inequality for (f, q = T/n); reason: given the history before phase i, the participating nodes choose bins independently and uniformly from [1, T], T = q_i n (Algorithm 10, line 6), and the paper's proof conditions on (7/8)f_{i−1} ≤ F_{i−1} ≤ f_{i−1}, which gives m ≤ f_{i−1}n; with f = f_{i−1}, T = q_i n, m = F_{i−1}n the statement is the lemma
--   - reading: "with high probability" → failure probability at most n^{−3}; reason: the paper's convention (failure ≤ n^{−C} for every C) cannot hold at the fixed threshold of Definition 31; the proof's n^{−6} applies the Chernoff bound Pr(X ≥ R) ≤ 2^{−R} for [0,1] summands to 2X_i, whose summands lie in [0,2]; applied to X_i with R = 3f²n/q ≥ 6E[X_i], the same argument gives at most n^{−3}
--   - encoding: log n → log₂ n; reason: the proof's step 2^{−6((7/8)f)²n/q} ≤ n^{−6} needs base 2
-- source:
--   Banasik, Dani, Hayes, Initialization with Exponentially Fewer Bits, STOC 2027 submission (manuscript, sha256 859ca50d…), full version Lemma 33, p.29 (PDF p.50), with Definitions 31–32 (p.29)

import Mathlib
import Definitions.Def_RadioInitBits_collidingNodes
import Definitions.Def_RadioInitBits_IsType1Phase

set_option autoImplicit false

namespace RadioInitBits

open scoped ENNReal

open Classical in
/-- **Lemma 33** (collisions in a type 1 phase), stated for the bin choices of one phase.
Let `n ≥ 0` be the number of nodes, let a phase have `T` bins (relative length `q = T / n`), and
let `f` be such that the type 1 condition `((7/8) f)² n / q ≥ log₂ n` of Definition 31 holds. If
`m ≤ f n` participating nodes each choose one of the `T` bins independently and uniformly at
random, then the probability that more than `6 f² n / q` of them collide (share their bin with
another participating node) is at most `n^{−3}`.
D. Banasik, V. Dani, T. P. Hayes, *Initialization with Exponentially Fewer Bits*, STOC 2027
submission (held version, sha256 859ca50d…), full version Lemma 33, p.29 (PDF p.50): "Let phase i
be a type 1 phase for some i > 6. Then, the true number of uninitialized nodes that collide is at
most 6f²_{i−1}n/q_i, with high probability."

**Formalization Note** In phase `i` of Algorithm 8 the `F_{i−1} n` participating uninitialized
nodes choose bins independently and uniformly from `[1, T]`, `T = q_i n` (Algorithm 10, line 6),
and the proof of Lemma 33 conditions on `(7/8) f_{i−1} ≤ F_{i−1} ≤ f_{i−1}`; given the history
before the phase, the lemma is this statement with `m = F_{i−1} n`, `f = f_{i−1}`, `T = q_i n`.
The statement is for arbitrary `f`, `T`, `m ≤ f n` (the lower bound `(7/8) f n ≤ m` is not
needed). "With high probability" is pinned as failure probability at most `n^{−3}` (log base 2).
The probability is the fraction of the `T^m` equally likely bin choices. -/
theorem lemma_33_type1_collisions (n m T : ℕ) (f : ℝ) (hup : (m : ℝ) ≤ f * n)
    (htype1 : IsType1 n f ((T : ℝ) / n)) :
    ((Finset.univ.filter fun x : Fin m → Fin T =>
        6 * f ^ 2 * n / ((T : ℝ) / n) < (collidingNodes x : ℝ)).card : ℝ≥0∞) / (T : ℝ≥0∞) ^ m
      ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 3) := by sorry

end RadioInitBits
