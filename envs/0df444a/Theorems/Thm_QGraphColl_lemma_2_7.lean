-- Prove2me | Theorems.Thm_QGraphColl_lemma_2_7
-- name    : QGraphColl.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:07.88012+00:00
-- url     : https://prove2.me/theorems/f92f0dce-15d1-4357-a92e-2d105e62c41f
-- title:
--   Lemma 2.7 — a cover of small marked volume: $\mathrm{cover\_test}(G,U,b)$ with $\tilde O(\sqrt{|U|}+\sqrt b)$ queries
-- statement:
--   Let $n=|V|\ge2$, let $U$ be a known vertex cover of $G$ and $b$ a real number. For every $c>0$ there are $C,K$ (independent of $V$, $G$, $U$, $b$) and a test with
--   $$T\le C\left(\sqrt{|U|}+\sqrt b\right)(\log_2 n)^K$$
--   queries which, with error at most $n^{-c}$, accepts every positive input and rejects every negative input with $\mathrm{vol}(G,U,x)\le b$.
--
--   This is the final test of the algorithm and the test of the edges discarded by thresholding.
--
--   Differences from the source:
--   - encoding: Õ(B) and 'the assigned error probability' → ∃ C, K (chosen after the error exponent c, before the vertex type and all parameters) with T ≤ C·B·(log₂ n)^K, n = |V| ≥ 2, and error ≤ n^{−c} for every c > 0; reason: the paper's conventions: Õ suppresses factors polynomial in log n and logarithms are base two (p.12); error probabilities are inverse polynomial in n (p.14)
--   - reading: the named procedure cover_test(G, U, b) (Algorithm 11) has the stated cost and guarantees → there is a T-query algorithm (QueryAlg, workspace Fin m) with that cost and those guarantees; reason: the procedure is a schema over black-box subroutines, so it is not one fixed object; the existence of a procedure with the printed cost and guarantees is what later proofs use (paper.md decision 4)
--   - encoding: volume bound b → b : ℝ of any sign; reason: for b < 0 the negative part of the domain is empty and √b = 0, so the claim only asks to accept positive inputs; for b ≥ 0 it is the source's statement
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma 2.7, p.14 (restated with proof, p.47; Algorithm 11 cover_test)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_vol
import Definitions.Def_QGraphColl_restrict
import Definitions.Def_QGraphColl_eventProb

open QAlgorithms

namespace QGraphColl

/-- **Lemma 2.7** (A cover of small marked volume; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.14, restated p.47). Let `U` be a known
vertex cover of `G`. The procedure `cover_test(G, U, b)` uses `Õ(√|U| + √b)` queries. It accepts
every positive input and rejects negative inputs satisfying `vol(G, U, x) ≤ b`.

**Formalization Note.**
* `Õ(B)` is `C · B · (log₂ n)^K` with `C, K` chosen after the error exponent `c` and before
  the vertex type and all parameters; "the assigned error probability" is `n^{-c}` for every `c > 0`
  (p.14: error probabilities are inverse polynomial in `n`), with `n = |V| ≥ 2`.
* The named procedure `cover_test` (Algorithm 11) is stated as the existence of a `T`-query
  algorithm with the printed cost and guarantee. "Accepts every positive input and rejects negative
  inputs satisfying the bound" is: it computes `gc G` with error `≤ n^{-c}` on the domain of all
  positive inputs and all negative inputs with `vol(G, U, x) ≤ b`.
* The bound `b` is real (Lemma 4.7 feeds the real `b_out`). For `b < 0` the negative part of the
  domain is empty and `√b = 0`; the claim then only asks to accept positive inputs. -/
theorem lemma_2_7 :
    ∀ c : ℝ, 0 < c → ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V], 2 ≤ Fintype.card V →
      ∀ (G : SimpleGraph V) (U : Finset V), IsCover G U → ∀ b : ℝ,
        ∃ T : ℕ, (T : ℝ) ≤ C * (Real.sqrt (U.card : ℝ) + Real.sqrt b) *
            Real.logb 2 (Fintype.card V : ℝ) ^ K ∧
          ∃ (m : ℕ) (A : QueryAlg V Bool (Fin m) T) (out : (V × Bool) × Fin m → Bool),
            A.ComputesWithError out
              (dom fun x => gc G x = true ∨ (gc G x = false ∧ (vol G U x : ℝ) ≤ b))
              (gc G) ((Fintype.card V : ℝ) ^ (-c)) := by sorry

end QGraphColl
