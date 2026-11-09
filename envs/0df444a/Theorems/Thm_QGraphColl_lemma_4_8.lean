-- Prove2me | Theorems.Thm_QGraphColl_lemma_4_8
-- name    : QGraphColl.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:49.022191+00:00
-- url     : https://prove2.me/theorems/aa935d4f-9ff6-4201-9404-3d5c4c195bed
-- title:
--   Lemma 4.8 — iterated volume reduction: bounded error with $\tilde O(\min\{\sqrt{nd},\max\{n^{13/22}d^{3/22},n^{1/2}d^{1/3}\}\})$ queries
-- statement:
--   **1. Query bound.** There are $C,K$ such that for every $n\ge2$, every real $1\le d\le n$ and every bipartite graph $G$ on at most $n$ labels of maximum degree at most $d$, some algorithm with
--   $$T\le C\min\Big\{\sqrt{nd},\ \max\big\{n^{13/22}d^{3/22},\ n^{1/2}d^{1/3}\big\}\Big\}(\log_2 n)^K$$
--   queries decides graph collision on $G$ with error at most $1/3$ on every input.
--
--   **2. Parameter choices.** For every constant $c>0$ of (4.4) and every constant $C_j$ there is $K_0$ such that for every $K\ge K_0$ the following holds. Let $n\ge2$, $1\le d\le n$, $T=\max\{n^{13/22}d^{3/22},n^{1/2}d^{1/3}\}$, $t=K\log_2^{10}(2n)\,T$ with $t<\sqrt{nd}$, $s=(nd)^{3/2}/t^3$, $\gamma=32(\log_2n)^2$, $t^2<\ell\le nd$, $1\le j\le C_j(\log_2n)^3$, and a piece with side sizes $1\le a,b\le n$, $m$ edges with $t^2<m\le\min\{a,b\}d$, and degree bounds $d_A,d_B\le d$ with $ad_A\le\gamma m$, $bd_B\le\gamma m$. Then the parameters (4.4)
--   $$p=\min\{1,\gamma\ell/m\},\quad\delta=\frac{c\ell t^2}{j^2\gamma^2ab},\quad\theta_A=\frac{a\sqrt p}{t},\quad\theta_B=\frac{b\sqrt p}{t},\quad s_A=s\sqrt{b/a},\quad s_B=s\sqrt{a/b}$$
--   satisfy $s_A,s_B\ge1$ and $v_A=2s_A\theta_Ad_A\le\delta^2$, $v_B=2s_B\theta_Bd_B\le\delta^2$.
--
--   Part 1 is the low-degree half of the algorithm (Algorithm 10); part 2 says its calls to reduce_volume meet the input conditions of Algorithm 9.
--
--   Differences from the source:
--   - reading: the named procedure Algorithm 10 (collision search with bounded maximum degree) has the stated cost and guarantees → there is a T-query algorithm (QueryAlg, workspace Fin m) with that cost and those guarantees; reason: the procedure is a schema over black-box subroutines, so it is not one fixed object; the existence of a procedure with the printed cost and guarantees is what later proofs use (paper.md decision 4)
--   - encoding: decides graph collision with bounded error … using Õ(min{…}) queries, n a bound on the number of labels → error ≤ 1/3 on every input; ∃ C, K before n, d, G with T ≤ C·min{…}·(log₂ n)^K, n ≥ 2, |V| ≤ n; reason: bounded error is error 1/3 (p.12); Õ suppresses polylog n (p.12)
--   - reading: its parameter choices satisfy s_A, s_B ≥ 1 and v_A, v_B ≤ δ² in every call to reduce_volume → the arithmetic implication of part 2 under the hypotheses Algorithm 10, (4.4), Lemma C.1 and Lemma C.2 supply for each call; reason: these are exactly the facts the proof (p.30) uses for a piece passed to reduce_volume (paper.md decision 8)
--   - generalization: c a sufficiently small absolute constant, K a sufficiently large absolute constant → for every c > 0 and every C_j > 0, every sufficiently large K; reason: the source fixes one small c; the Lean holds for each c, which specializes to the source's
--   - reading: degree bound d with 1 ≤ d ≤ n (type not stated) → d : ℝ; reason: the paper uses d as a real parameter in its cost exponents; every integer d (Theorem 1.1 takes d = ⌈n^{7/17}⌉) is an instance, so no case is dropped
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma 4.8, p.30 (Algorithm 10 and the parameters (4.4), p.29; proof pp.30–31)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_vol
import Definitions.Def_QGraphColl_restrict

open QAlgorithms

namespace QGraphColl

/-- **Lemma 4.8** (Iterated volume reduction; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall,
S. Patro, X. Zhou, *Breaking the quantum barriers for Graph Collision*, arXiv:2611.05356 (version of
October 2026, sha256 21da7ff0…), p.30). Algorithm 10 decides graph collision with bounded error for
bipartite graphs on at most `n` labels of maximum degree at most `d`, using
`Õ(min{√(nd), max{n^{13/22} d^{3/22}, n^{1/2} d^{1/3}}})` queries. Its parameter choices satisfy
`s_A, s_B ≥ 1` and `v_A, v_B ≤ δ²` in every call to `reduce_volume`.

**Formalization Note.**
* First clause: Algorithm 10 is stated as the existence of a `T`-query algorithm with the printed
  cost that computes `gc G` with error `≤ 1/3` ("bounded error") on every input. Here `n ≥ 2` is the
  stated bound on the number of labels (`|V| ≤ n`), `1 ≤ d ≤ n` is real, `Õ` hides `(log₂ n)^K`, and
  `C, K` are chosen before `n`, `d` and the graph.
* Second clause (the parameter choices): the arithmetic fact the proof (p.30) establishes for every
  piece Algorithm 10 passes to `reduce_volume`. With `T = max{n^{13/22} d^{3/22}, n^{1/2} d^{1/3}}`,
  `t = K log₂^{10}(2n) T` (Algorithm 10, line 1), in the branch `t < √(nd)` (line 2),
  `s = (nd)^{3/2}/t³` (line 3), at a volume bound `ℓ` with `t² < ℓ ≤ nd` (the loop, lines 4–5),
  with `j ≤ C_j (log₂ n)³` pieces (Lemma C.2), `γ = 32 (log₂ n)²`, and a piece with side sizes
  `1 ≤ a, b ≤ n`, `m` edges with `t² < m ≤ min{a, b}·d` (line 8 discards smaller pieces; maximum
  degree `≤ d`), and degree bounds `d_A, d_B ≤ d` with `a d_A ≤ γ m`, `b d_B ≤ γ m` (Lemma C.1),
  the parameters (4.4), p.29, `p = min{1, γℓ/m}`, `δ = cℓt²/(j²γ²ab)`, `θ_A = a√p/t`, `θ_B = b√p/t`,
  `s_A = s√(b/a)`, `s_B = s√(a/b)`, satisfy `s_A, s_B ≥ 1` and `v_A = 2 s_A θ_A d_A ≤ δ²`,
  `v_B = 2 s_B θ_B d_B ≤ δ²`. The constants are quantified as the paper fixes them: for every
  constant `c > 0` of (4.4) and every constant `C_j` of Lemma C.2, every sufficiently large `K`
  works. -/
theorem lemma_4_8 :
    (∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧
      ∀ n : ℕ, 2 ≤ n → ∀ d : ℝ, 1 ≤ d → d ≤ (n : ℝ) →
      ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V ≤ n →
      ∀ (G : SimpleGraph V) (A B : Finset V), IsSides G A B → (∀ v, (deg G v : ℝ) ≤ d) →
        ∃ T : ℕ, (T : ℝ) ≤ C * min (Real.sqrt ((n : ℝ) * d))
              (max ((n : ℝ) ^ ((13 : ℝ) / 22) * d ^ ((3 : ℝ) / 22))
                ((n : ℝ) ^ ((1 : ℝ) / 2) * d ^ ((1 : ℝ) / 3))) * Real.logb 2 (n : ℝ) ^ K ∧
          ∃ (m : ℕ) (Alg : QueryAlg V Bool (Fin m) T) (out : (V × Bool) × Fin m → Bool),
            Alg.ComputesWithError out Finset.univ (gc G) (1 / 3)) ∧
    (∀ c : ℝ, 0 < c → ∀ Cj : ℝ, 0 < Cj → ∃ K₀ : ℝ, ∀ K : ℝ, K₀ ≤ K →
      ∀ n : ℕ, 2 ≤ n → ∀ d : ℝ, 1 ≤ d → d ≤ (n : ℝ) →
        let T : ℝ := max ((n : ℝ) ^ ((13 : ℝ) / 22) * d ^ ((3 : ℝ) / 22))
          ((n : ℝ) ^ ((1 : ℝ) / 2) * d ^ ((1 : ℝ) / 3))
        let t : ℝ := K * Real.logb 2 (2 * (n : ℝ)) ^ 10 * T
        t < Real.sqrt ((n : ℝ) * d) →
        let s : ℝ := ((n : ℝ) * d) ^ ((3 : ℝ) / 2) / t ^ 3
        let γ : ℝ := 32 * Real.logb 2 (n : ℝ) ^ 2
        ∀ ℓ : ℝ, t ^ 2 < ℓ → ℓ ≤ (n : ℝ) * d →
        ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ Cj * Real.logb 2 (n : ℝ) ^ 3 →
        ∀ (a b m : ℕ) (dA dB : ℝ), 1 ≤ a → a ≤ n → 1 ≤ b → b ≤ n →
          t ^ 2 < (m : ℝ) → (m : ℝ) ≤ min (a : ℝ) (b : ℝ) * d →
          dA ≤ d → dB ≤ d → (a : ℝ) * dA ≤ γ * m → (b : ℝ) * dB ≤ γ * m →
          let p : ℝ := min 1 (γ * ℓ / m)
          let δ : ℝ := c * ℓ * t ^ 2 / ((j : ℝ) ^ 2 * γ ^ 2 * a * b)
          let θA : ℝ := a * Real.sqrt p / t
          let θB : ℝ := b * Real.sqrt p / t
          let sA : ℝ := s * Real.sqrt ((b : ℝ) / a)
          let sB : ℝ := s * Real.sqrt ((a : ℝ) / b)
          1 ≤ sA ∧ 1 ≤ sB ∧ 2 * sA * θA * dA ≤ δ ^ 2 ∧ 2 * sB * θB * dB ≤ δ ^ 2) := by sorry

end QGraphColl
