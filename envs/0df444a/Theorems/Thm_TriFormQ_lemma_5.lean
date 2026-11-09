-- Prove2me | Theorems.Thm_TriFormQ_lemma_5
-- name    : TriFormQ.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:47:00.417566+00:00
-- url     : https://prove2.me/theorems/c40a74fa-fb9e-42e1-9c17-9fef186125aa
-- title:
--   Lemma 5 (Learning-Low-Rank-Matrix): $r+\lceil\log_q(1/\varepsilon)\rceil$ RightMult and $r$ LeftMult queries learn a rank-$\le r$ matrix
-- statement:
--   Let $M\in M_n(\mathbb F_q)$ be accessible only through the classical matrix–vector queries $\mathrm{RightMult}:y\mapsto My$ and $\mathrm{LeftMult}:x\mapsto x^\top M$. For every $r\ge 0$ and $0<\varepsilon<1$ there is a randomized algorithm, depending on $n$, $r$ and $\varepsilon$ only, such that for every $M$:
--
--   1. on every run it makes at most $r+\lceil\log_q(1/\varepsilon)\rceil$ RightMult queries and at most $r$ LeftMult queries;
--   2. if $\mathrm{rk}(M)\le r$, it returns $N=M$ with probability at least $1-\varepsilon$.
--
--   This subroutine learns low-rank matrices with a number of queries independent of $n$; it is used for the slices in Theorems 4, 6 and 7.
--
--   **Formalization Note** A randomized classical algorithm is a probability distribution over the platform's deterministic decision trees on the input `matOracle M`.
--
--   Differences from the source:
--   - encoding: makes $r+\lceil\log_q\frac1\varepsilon\rceil$ RightMult queries → makes at most $r+\lceil\log_q\frac1\varepsilon\rceil$ RightMult queries; reason: making fewer queries is never harder; Fig. 3 makes exactly that many
--   - generalization: the query counts, stated under the promise $\mathrm{rk}(M)\le r$ → the query counts hold for every $M$; correctness under the promise; reason: Fig. 3 aborts at step (3) when the rank bound is exceeded, so its counts hold on every input; restricted to $\mathrm{rk}(M)\le r$ this is the source's claim
--   - encoding: a randomized algorithm with RightMult and LeftMult access → a `PMF` over decision trees on `matOracle M`, counting the two kinds of queries on each tree of the support; reason: platform classical query model
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 5, p.17 (PDF p.20)

import Definitions.Def_TriFormQ_matOracle
import Definitions.Def_TriFormQ_queriesWhere

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 5, p.17 (PDF p.20): "Let
M ∈ M_n(𝔽_q) be an n × n matrix over 𝔽_q given as a black box oracle function. The only access
to M is through matrix-vector multiplication queries RightMult : 𝔽_q^n → 𝔽_q^n, y ↦ My and
LeftMult : 𝔽_q^n → 𝔽_q^n, x ↦ xᵀM. If we are promised that rk(M) ≤ r, then for any 0 < ε < 1
there is a randomized algorithm that makes r + ⌈log_q 1/ε⌉ RightMult queries, at most r LeftMult
queries and returns a matrix N such that N = M with probability at least 1 − ε."

**Formalization Note.** A randomized classical algorithm is a distribution over the platform's
decision trees on the input `matOracle M` (`Sum.inl y` = RightMult at `y`, `Sum.inr x` =
LeftMult at `x`), chosen from `n`, `r`, `ε` before `M`. "Makes r + ⌈log_q 1/ε⌉ RightMult queries"
is read as at most that many. The two query counts are bounded on every tree of the support and
for every `M` (Fig. 3 aborts at step (3) when the rank bound is exceeded); correctness is
required under the promise `rk M ≤ r`. -/
theorem lemma_5 {F : Type} [Field F] [Fintype F] [DecidableEq F] (n r : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) :
    ∃ R : QAlgorithms.RandDecisionTree (Vec F n ⊕ Vec F n) (Vec F n) (Matrix (Fin n) (Fin n) F),
      ∀ M : Matrix (Fin n) (Fin n) F,
        (∀ t ∈ R.support,
          queriesWhere (fun i => i.isLeft = true) t (matOracle M) ≤
              r + ⌈Real.logb (Fintype.card F) (1 / ε)⌉₊ ∧
            queriesWhere (fun i => i.isRight = true) t (matOracle M) ≤ r) ∧
        (M.rank ≤ r → 1 - ε ≤ QAlgorithms.successProb R (matOracle M) M) := by sorry

end TriFormQ
