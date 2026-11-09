-- Prove2me | Theorems.Thm_TriFormQ_theorem_1
-- name    : TriFormQ.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:49:27.685249+00:00
-- url     : https://prove2.me/theorems/ebe4ea87-5b3e-415c-aea3-be1c6c035006
-- title:
--   Theorem 1 (Main): every list of $L$ trilinear forms over $\mathbb F_q$ is identified with $O_q(\log^{2/3}L\cdot\lambda(\delta))$ quantum queries (corrected: $\max\{1,\log_2(1/\delta)\}$)
-- statement:
--   Let $\mathbb F_q$ be a finite field ($q$ a prime power). There is a constant $C$, depending only on $q$, such that the following holds for all positive integers $n$ and $L$, every explicitly given list $T^1,\dots,T^L$ of trilinear forms on $\mathbb F_q^n$ (repetitions allowed) and every $0<\delta<1$. There is a randomized quantum query algorithm, depending on the list and $\delta$ but not on the hidden index, such that for every $i\in[L]$, when given the evaluation oracle $|x,y,z,b\rangle\mapsto|x,y,z,b+T^i(x,y,z)\rangle$ of the unknown form $f=T^i$:
--
--   1. every run of positive probability makes at most
--   $$C\,(\log_2 L)^{2/3}\cdot\max\{1,\log_2(1/\delta)\}$$
--   queries to the oracle;
--   2. with probability at least $1-\delta$ it outputs an index $j$ with $T^j=f$.
--
--   The bound is independent of the dimension $n$ and grows like $\log^{2/3}L$, below the classical information-theoretic $\log_q L$ for every class of trilinear forms; a matching $\Omega(\log^{2/3}L)$ lower bound holds for some classes (Theorem 3 of the paper).
--
--   Differences from the source:
--   - correction: $O_q(\log^{2/3}L\cdot\log\frac1\delta)$ → $C(\log_2L)^{2/3}\max\{1,\log_2(1/\delta)\}$; reason: for every $C$: $q=2$, $L=2^k$ distinct forms on $\mathbb F_2^k$, $\log_2(1/\delta)=1/(2Ck^{2/3})$ allow fewer than one query, and a 0-query algorithm outputs some $i$ with probability $\le2^{-k}<1-\delta$ for large $k$; identical for $\delta\le1/2$
--   - encoding: $O_q(\cdot)$, $\log^{2/3}L$ → one constant $C$ per finite field, chosen before $n$, $L$, the list and $\delta$; $(\log_2L)^{2/3}$; reason: the paper's logarithm convention (p.10)
--   - encoding: $q$ a prime power, $\mathbb F_q$ → every finite field `F` with $q=|F|$; reason: the finite fields are exactly the $\mathbb F_q$
--   - encoding: correctly identifies $f$ in $\mathcal T$ → outputs an index $j$ with $T^j=T^i$; reason: the list may contain repetitions
--   - reading: there is a randomized quantum query algorithm (for the unknown $f$ among explicitly given forms) → the algorithm is chosen after the list and $\delta$ and before the hidden index $i$; its query count is the worst case over positive-probability runs on the oracle of $T^i$; reason: an algorithm chosen after $i$ would output $i$ with no query
--   - encoding: randomized quantum query algorithm making at most $X$ queries → an `AdaptiveAlg` (rounds of the platform's `QueryAlg` against the standard oracle, full measurement, classical choice of the next round) chosen before the oracle, whose worst-case query count over positive-probability runs on that oracle is at most $X$; reason: platform query model; classical coins are 0-query rounds and offline computation on explicit data is free, as in the paper
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 1 (Main), p.3 (PDF p.6)

import Definitions.Def_TriFormQ_oracle
import Definitions.Def_TriFormQ_AdaptiveAlg_outProb
import Definitions.Def_TriFormQ_AdaptiveAlg_maxQueries
import Definitions.Def_TriFormQ_lam

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 1 (Main), p.3
(PDF p.6): "Let q be a prime power, n and L be positive integers, and T = {T¹, …, T^L} be a list
of L explicitly given trilinear forms on an n-dimensional vector space over 𝔽_q. Let f be an
unknown trilinear form T (i.e., f = Tⁱ for some i ∈ {1, 2, …, L}) to which we are granted quantum
query access an oracle for f. Then, for any 0 < δ < 1, there is a randomized quantum query
algorithm that makes at most O_q(log^{2/3} L · log(1/δ)) queries to the oracle and correctly
identifies f in T with probability at least 1 − δ."

**Formalization Note.** For every finite field `F` (`q = |F|`, a prime power) there is one
constant `C`, chosen before `n`, `L`, the list and `δ`; the bound does not depend on `n`.
`log^{2/3} L` is `(log₂ L)^{2/3}` (logarithms base 2, p.10), and `log(1/δ)` is corrected to
`λ(δ) = max{1, log₂(1/δ)}` (see the item's differences). The algorithm is an `AdaptiveAlg` with
the standard oracle of `f`, chosen from the explicit list and `δ` before the hidden index `i`;
`maxQueries` is the worst case over runs of positive probability on that oracle. "Identifies f
in T" is outputting an index `j` with `Tʲ = Tⁱ` (the list may contain repetitions). -/
theorem theorem_1 :
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], ∃ C : ℝ, ∀ n L : ℕ, 0 < n → 0 < L →
      ∀ (T : Fin L → TriForm F n) (δ : ℝ), 0 < δ → δ < 1 →
        ∃ A : AdaptiveAlg (Vec F n × Vec F n × Vec F n) F (Fin L), ∀ i : Fin L,
          (A.maxQueries (oracle (T i)) : ℝ) ≤ C * (Real.logb 2 L) ^ ((2 : ℝ) / 3) * lam δ ∧
          1 - δ ≤ A.outProb (oracle (T i)) (fun j => T j = T i) := by sorry

end TriFormQ
