-- Prove2me | Theorems.Thm_QGraphColl_lemma_4_7
-- name    : QGraphColl.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:12:04.610899+00:00
-- url     : https://prove2.me/theorems/7653182a-8e24-46fd-89e9-56084729b469
-- title:
--   Lemma 4.7 — piece reduction: volume $a\tau_A+b\tau_B+O(\sqrt{abp\delta})$, outside cover $b_{\mathrm{out}}$, cost $\tilde O(Q)$
-- statement:
--   Let $n=|V|\ge2$ and let $G$ satisfy the input conditions of Algorithm 9: bipartite with sides $A,B$ of sizes $a,b$, degree bounds $d_A,d_B$, $m$ edges, a marked fraction bound $p\in[0,1]$, parameters $\theta_A,\theta_B,\delta,\tau_A,\tau_B>0$ and $s_A,s_B\ge1$, with $v_A=2s_A\theta_Ad_A\le\delta^2$ and $v_B=2s_B\theta_Bd_B\le\delta^2$. There are absolute constants $c_0,C_1$ and, for every $c>0$, constants $C,K$, such that some algorithm with $T\le C\,Q\,(\log_2 n)^K$ queries, where
--   $$b_{\mathrm{out}}=c_0p\delta\left(\frac{d_Ab}{\tau_A^2}+\frac{d_Ba}{\tau_B^2}\right),\qquad Q=\sqrt{a+b}+\frac{a\sqrt p}{\theta_A}+\frac{b\sqrt p}{\theta_B}+Q_{\mathrm{extract}}+\frac{\sqrt p\,(av_A+bv_B)}{\delta^2}+\sqrt{b_{\mathrm{out}}},$$
--   $$Q_{\mathrm{extract}}=\sqrt m\Big[s_A^{-1/3}(\theta_B/\theta_A)^{1/6}+s_B^{-1/3}(\theta_A/\theta_B)^{1/6}+s_A^{-1/2}+s_B^{-1/2}+\sqrt{d_A/\delta}+\sqrt{d_B/\delta}\Big],$$
--   reports a collision or returns a preprocessed graph $G_{\mathrm{pre}}\subseteq G$ and a set $P$, with output graph $G_{\mathrm{pre}}[P]$, such that:
--
--   1. on every negative input with $|M\cap A|\le ap$ and $|M\cap B|\le bp$, with probability at least $1-n^{-c}$ the output has marked volume at most $a\tau_A+b\tau_B+C_1\sqrt{abp\delta}$, and the edges $G_{\mathrm{pre}}\setminus G_{\mathrm{pre}}[P]$ discarded after estimating the counts have the cover $V\setminus P$ of marked volume at most $b_{\mathrm{out}}$;
--   2. on every positive input, with probability at least $1-n^{-c}$ a collision is reported or survives in the output.
--
--   This is one round of volume reduction on one piece of the partition (Algorithm 9, reduce_volume).
--
--   Differences from the source:
--   - encoding: O(√(abpδ)), 'sufficiently large absolute constant c₀', Õ(Q) and the assigned error → absolute C₁, c₀ > 0 chosen first; then for every c > 0, C, K with T ≤ C·Q·(log₂ n)^K and error ≤ n^{−c}, n = |V| ≥ 2; reason: the paper's conventions (pp.12, 14)
--   - reading: the named procedure Algorithm 9 (reduce_volume) has the stated cost and guarantees → there is a T-query algorithm (QueryAlg, workspace Fin m) with that cost and those guarantees; reason: the procedure is a schema over black-box subroutines, so it is not one fixed object; the existence of a procedure with the printed cost and guarantees is what later proofs use (paper.md decision 4)
--   - reading: on a good negative execution … the output has marked volume at most …; the edges discarded after estimating the counts have a cover of marked volume at most b_out → output some (G_pre, P) with G_pre ≤ G; on every negative input with the count bounds, with probability ≥ 1 − n^{−c}, vol(G_pre[P], x) ≤ aτ_A + bτ_B + C₁√(abpδ), V \ P covers G_pre \ G_pre[P] and its marked volume there is ≤ b_out; reason: good executions have probability ≥ 1 − ε (proof, p.29); the cover is the one Algorithm 9 tests (line 6)
--   - generalization: G bipartite with vertex sets A and B (V(G) = A ∪ B) → IsSides G A B on a vertex type that may contain further labels outside A ∪ B; reason: labels outside A ∪ B are isolated; taking V = A ∪ B gives the source's statement
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma 4.7, pp.28–29 (Algorithm 9 reduce_volume and its input conditions, p.28)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_vol
import Definitions.Def_QGraphColl_restrict
import Definitions.Def_QGraphColl_eventProb

open QAlgorithms

namespace QGraphColl

/-- **Lemma 4.7** (Piece reduction; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro,
X. Zhou, *Breaking the quantum barriers for Graph Collision*, arXiv:2611.05356 (version of October
2026, sha256 21da7ff0…), pp.28–29). Let `G` have `m` edges and satisfy the input conditions of
Algorithm 9. Suppose `|M ∩ A| ≤ ap` and `|M ∩ B| ≤ bp` on the negative inputs under consideration.
On a good negative execution the output has marked volume at most `aτ_A + bτ_B + O(√(abpδ))`. On
the same good negative execution, the edges discarded after estimating the counts have a cover of
marked volume at most `b_out = c₀ p δ (d_A b/τ_A² + d_B a/τ_B²)`, for a sufficiently large absolute
constant `c₀`. The query complexity is `Õ(Q)`, where
`Q = √(a + b) + a√p/θ_A + b√p/θ_B + Q_extract + √p (a v_A + b v_B)/δ² + √b_out`,
`Q_extract = √m [s_A^{-1/3}(θ_B/θ_A)^{1/6} + s_B^{-1/3}(θ_A/θ_B)^{1/6} + s_A^{-1/2} + s_B^{-1/2}
+ √(d_A/δ) + √(d_B/δ)]`. On a positive input, a collision is detected or survives, except with the
assigned error.

**Formalization Note.**
* Input conditions of Algorithm 9 (p.28): `G` bipartite with sides `A, B` of sizes `a, b`, degree
  bounds `d_A, d_B`, `p ∈ [0, 1]`, `θ_A, θ_B, δ, τ_A, τ_B > 0`, `s_A, s_B ≥ 1`, and
  `v_A = 2 s_A θ_A d_A ≤ δ²`, `v_B = 2 s_B θ_B d_B ≤ δ²`.
* The absolute constants `c₀` (in `b_out`) and `C₁` (of `O(√(abpδ))`) come first; then the error
  exponent `c`, then `C, K` of `Õ(Q) = C · Q · (log₂ n)^K`, `n = |V| ≥ 2`; "the assigned error" is
  `n^{-c}`.
* Algorithm 9 (`reduce_volume`) is stated as the existence of a `T`-query algorithm. Its output is
  `none` ("Yes": collision detected) or `some (G_pre, P)`: the graph `G_pre ≤ G` after the
  preprocessing (lines 1–2) and the threshold set `P` (line 5). The returned graph is `G_pre[P]`
  (`restrict G_pre P`, line 7), and the discarded edges are `G_pre \ G_pre[P]` with cover `V \ P`
  (line 6); marked volumes are taken with degrees in these edge sets.
* "On a good negative execution": on every negative input with `|M ∩ A| ≤ ap`, `|M ∩ B| ≤ bp`, with
  probability `≥ 1 − n^{-c}` both volume bounds hold. On every positive input, with probability
  `≥ 1 − n^{-c}` a collision is detected or survives in the returned graph.
* Labels outside `A ∪ B` are allowed (isolated). -/
theorem lemma_4_7 :
    ∃ c₀ C₁ : ℝ, 0 < c₀ ∧ 0 < C₁ ∧ ∀ c : ℝ, 0 < c → ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V], 2 ≤ Fintype.card V →
      ∀ (G : SimpleGraph V) (A B : Finset V), IsSides G A B →
      ∀ (dA dB : ℝ), (∀ v ∈ A, (deg G v : ℝ) ≤ dA) → (∀ w ∈ B, (deg G w : ℝ) ≤ dB) →
      ∀ (p θA θB δ τA τB sA sB : ℝ), 0 ≤ p → p ≤ 1 → 0 < θA → 0 < θB → 0 < δ →
        0 < τA → 0 < τB → 1 ≤ sA → 1 ≤ sB →
        2 * sA * θA * dA ≤ δ ^ 2 → 2 * sB * θB * dB ≤ δ ^ 2 →
        let a : ℝ := A.card
        let b : ℝ := B.card
        let mE : ℝ := numEdges G
        let vA : ℝ := 2 * sA * θA * dA
        let vB : ℝ := 2 * sB * θB * dB
        let bout : ℝ := c₀ * p * δ * (dA * b / τA ^ 2 + dB * a / τB ^ 2)
        let Qext : ℝ := Real.sqrt mE *
          (sA ^ (-(1 : ℝ) / 3) * (θB / θA) ^ ((1 : ℝ) / 6) +
            sB ^ (-(1 : ℝ) / 3) * (θA / θB) ^ ((1 : ℝ) / 6) +
            sA ^ (-(1 : ℝ) / 2) + sB ^ (-(1 : ℝ) / 2) + Real.sqrt (dA / δ) + Real.sqrt (dB / δ))
        let Q : ℝ := Real.sqrt (a + b) + a * Real.sqrt p / θA + b * Real.sqrt p / θB + Qext +
          Real.sqrt p * (a * vA + b * vB) / δ ^ 2 + Real.sqrt bout
        ∃ T : ℕ, (T : ℝ) ≤ C * Q * Real.logb 2 (Fintype.card V : ℝ) ^ K ∧
          ∃ (m : ℕ) (Alg : QueryAlg V Bool (Fin m) T)
            (out : (V × Bool) × Fin m → Option (SimpleGraph V × Finset V)),
            (∀ z Gp P, out z = some (Gp, P) → Gp ≤ G) ∧
            (∀ x : V → Bool, gc G x = false →
              ((marked x ∩ A).card : ℝ) ≤ a * p → ((marked x ∩ B).card : ℝ) ≤ b * p →
              eventProb Alg x out (fun o => ∃ Gp P, o = some (Gp, P) ∧
                (vol (restrict Gp P) Finset.univ x : ℝ) ≤
                  a * τA + b * τB + C₁ * Real.sqrt (a * b * p * δ) ∧
                IsCover (Gp \ restrict Gp P) (Finset.univ \ P) ∧
                (vol (Gp \ restrict Gp P) (Finset.univ \ P) x : ℝ) ≤ bout)
                ≥ 1 - (Fintype.card V : ℝ) ^ (-c)) ∧
            (∀ x : V → Bool, gc G x = true →
              eventProb Alg x out (fun o => o = none ∨
                ∃ Gp P, o = some (Gp, P) ∧ gc (restrict Gp P) x = true)
                ≥ 1 - (Fintype.card V : ℝ) ^ (-c)) := by sorry

end QGraphColl
