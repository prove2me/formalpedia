-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_lemma_10
-- name    : TarskiQuasiFPT.UpperBound.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:41.423859+00:00
-- url     : https://prove2.me/theorems/5b817ff3-fdaa-4154-a565-f877898186c5
-- title:
--   Lemma 10 — a heavy antipodal set-pair exists whenever $R(Q)\neq\emptyset$
-- statement:
--   Let $Q$ be a safe query-answer set with $R(Q)\ne\emptyset$, the bad pairs taken along coordinate $k$. There are $S^-\subseteq\mathrm{Fix}^-(Q)$ and $S^+\subseteq\mathrm{Fix}^+(Q)$ such that:
--
--   1. $(S^-,S^+)$ is **heavy**:
--   $$\bigl|\{(x,y)\in R(Q): x\in S^-\}\bigr|\ \ge\ \frac{|R(Q)|}{2^k},\qquad \bigl|\{(x,y)\in R(Q): y\in S^+\}\bigr|\ \ge\ \frac{|R(Q)|}{2^k};$$
--   2. $(S^-,S^+)$ is **antipodal**: there are a partition $[k]=J\sqcup H$ with $k\in H$ and $t\in[n]^k$ such that $x_J\preceq t_J\preceq y_J$ and $x_H\succeq t_H\succeq y_H$ for all $x\in S^-$, $y\in S^+$, and $x_k\ge t_k+1$ for every $x\in S^-$.
--
--   Each round of Theorem 5 eliminates one side of such a pair, removing a $2^{-k}$ fraction of the bad pairs.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: n ≥ 1 (standing: [n] is nonempty) → type-class hypothesis [NeZero n]; reason: the same condition, needed so that J_s(Q), M_s(Q) (a finite join/meet of grid points) are defined
--   - encoding: query-answer set: a finite set of pairs (x, r) with distinct x; Q ⊆ Q′ as sets of pairs → QASet n k = Point n k → Option (Point n k × Label) (Q x = some r iff (x, r) ∈ Q); QASubset Q Q′ is inclusion of recorded pairs; reason: a partial function on the finite grid is exactly a finite set of pairs with distinct first components
--   - encoding: coordinate k (the last coordinate) → c : Fin k with c + 1 = k; reason: c is exactly the last coordinate in 0-based indexing; c + 1 = k also encodes k ≥ 1
--   - encoding: |{…}| ≥ |R(Q)|/2^k → |R(Q)| ≤ 2^k · |{…}| in ℕ; reason: multiplying out by 2^k > 0 changes no instance
--   - encoding: partition [k] = J ⊍ H with k ∈ H; x_k ≥ t_k + 1 → a finset J of coordinates with c ∉ J, H its complement; t_c < x_c; reason: a partition is determined by J; for integers x_k ≥ t_k + 1 iff t_k < x_k
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Lemma 10, PDF pp. 10–11 (printed pp. 9–10)

import Mathlib
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets

set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound

/-- Lemma 10 (PDF pp. 10–11): let `Q` be a safe query-answer set with `R(Q) ≠ ∅` (bad pairs along
the last coordinate `c`). There are `S⁻ ⊆ Fix⁻(Q)` and `S⁺ ⊆ Fix⁺(Q)` such that
(i) `|{(x, y) ∈ R(Q) : x ∈ S⁻}| ≥ |R(Q)|/2^k` and `|{(x, y) ∈ R(Q) : y ∈ S⁺}| ≥ |R(Q)|/2^k`
(stated multiplied out), and (ii) `(S⁻, S⁺)` is antipodal. -/
theorem lemma_10 {n k : ℕ} [NeZero n] (c : Fin k) (hc : (c : ℕ) + 1 = k)
    (Q : QASet n k) (hQ : IsSafeQA Q) (hR : (badPairs Q c).Nonempty) :
    ∃ Sm Sp : Finset (Point n k), Sm ⊆ FixMinus Q ∧ Sp ⊆ FixPlus Q ∧
      (badPairs Q c).card ≤ 2 ^ k * ((badPairs Q c).filter fun p => p.1 ∈ Sm).card ∧
      (badPairs Q c).card ≤ 2 ^ k * ((badPairs Q c).filter fun p => p.2 ∈ Sp).card ∧
      IsAntipodal c Sm Sp := by sorry

end TarskiQuasiFPT.UpperBound
