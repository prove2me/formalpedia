-- Prove2me | Theorems.Thm_TriFormQ_theorem_4
-- name    : TriFormQ.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:47:19.69131+00:00
-- url     : https://prove2.me/theorems/98a49075-7dff-49de-8ddb-c51f4a356753
-- title:
--   Theorem 4: identifying a bilinear form from a list of $L$ with $O_q(\sqrt{\log L}+\log(1/\varepsilon))$ quantum queries
-- statement:
--   Let $\mathbb F_q$ be a finite field. There is a constant $C$ (depending only on $q$) such that for every $n$, $L$, every explicitly given list $M^1,\dots,M^L$ of $n\times n$ matrices over $\mathbb F_q$ and every $0<\varepsilon<1$ there is a randomized quantum query algorithm, depending on the list and $\varepsilon$ only, with the following property. For every matrix $M$, given the evaluation oracle of $f(x,y)=x^\top My$, the algorithm
--
--   1. makes at most $C\big(\sqrt{\log_2 L}+\log_2(1/\varepsilon)\big)$ queries on every run;
--   2. if $M=M^i$ for some $i$, outputs an index $j$ with $M^j=M$ with probability at least $1-\varepsilon$;
--   3. if $M$ is not in the list, outputs "not in the list" with probability at least $1-\varepsilon$.
--
--   This worst-case matrix identification is the building block of the weighted-list algorithm (Theorem 5) and of the slice-by-slice identification of trilinear forms.
--
--   Differences from the source:
--   - encoding: identifies $f$; detects that $M$ is not in the list → outputs `some j` with $M^j=M$ (any such index: the list may repeat); outputs `none`; reason: output convention
--   - encoding: $O_q(\sqrt{\log L}+\log\frac1\varepsilon)$ → one constant $C$ depending only on $\mathbb F_q$, chosen before $n$, $L$, the list and $\varepsilon$; logarithms base 2; reason: the paper's logarithm convention (p.10); base changes are absorbed in $C$
--   - encoding: randomized quantum query algorithm making at most $X$ queries → an `AdaptiveAlg` (rounds of the platform's `QueryAlg` against the standard oracle, full measurement, classical choice of the next round) chosen before the oracle, whose worst-case query count over positive-probability runs on that oracle is at most $X$; reason: platform query model; classical coins are 0-query rounds and offline computation on explicit data is free, as in the paper
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 4, p.18 (PDF p.21)

import Definitions.Def_TriFormQ_bilOracle
import Definitions.Def_TriFormQ_AdaptiveAlg_outProb
import Definitions.Def_TriFormQ_AdaptiveAlg_maxQueries

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 4, p.18 (PDF p.21): "Let
M = {M¹, …, M^L} be a list of L explicitly given bilinear forms on an n-dimensional vector space
over 𝔽_q. Let f(x, y) = xᵀMy be a black box bilinear form on the same vector space, to which
algorithm can only access by making evaluation queries. If we are promised that M = Mⁱ for some
i ∈ [L], then for any 0 < ε < 1 there is a randomized algorithm that makes at most
O_q(√(log L) + log(1/ε)) quantum queries and identifies f with probability at least 1 − ε.
Moreover, if the input oracle bilinear form M is not in the list M, our algorithm will detect
this with probability at least 1 − ε."

**Formalization Note.** One constant `C` depending only on the field, before `n`, `L`, the list
and `ε`; logarithms base 2. The algorithm outputs `some j` (identify `Mʲ`, which may be any
index of a matrix equal to `M`: the list may repeat) or `none` (detect "not in the list"). The
query bound holds on every oracle, in the list or not. -/
theorem theorem_4 {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    ∃ C : ℝ, ∀ (n L : ℕ) (Ms : Fin L → Matrix (Fin n) (Fin n) F) (ε : ℝ),
      0 < ε → ε < 1 →
      ∃ A : AdaptiveAlg (Vec F n × Vec F n) F (Option (Fin L)), ∀ M : Matrix (Fin n) (Fin n) F,
        (A.maxQueries (bilOracle M) : ℝ) ≤
            C * (Real.sqrt (Real.logb 2 L) + Real.logb 2 (1 / ε)) ∧
        ((∃ i, Ms i = M) →
          1 - ε ≤ A.outProb (bilOracle M) (fun o => ∃ j, o = some j ∧ Ms j = M)) ∧
        ((∀ i, Ms i ≠ M) → 1 - ε ≤ A.outProb (bilOracle M) (fun o => o = none)) := by sorry

end TriFormQ
