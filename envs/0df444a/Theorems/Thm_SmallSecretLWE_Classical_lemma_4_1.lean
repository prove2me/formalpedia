-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_lemma_4_1
-- name    : SmallSecretLWE.Classical.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:28:22.347527+00:00
-- url     : https://prove2.me/theorems/64b05aa8-e0dd-4c8b-921e-653fa262e5bb
-- title:
--   Lemma 4.1 — a vertex of $K_l(A)$ can be sampled exactly from $\nu$ in expected time $\tilde O(l)$
-- statement:
--   There are one randomized program and constants $K>0$, $c\in\mathbb N$ such that the following holds. Let $q\ge2$, $1\le k\le n$, $\lceil k/2\rceil\le l\le n$, and let $A\in\mathbb Z_q^{m\times n}$ have exactly $k$ nonzero entries in each row. Run on the sparse representations of the rows of $A$, the program outputs every vertex $v$ of $K_l(A)$ with probability exactly $\nu(v)=\text{out-deg}(v)/|E(K_l(A))|$, and its expected cost is
--   $$\mathbb E[\text{cost}]\ \le\ K\cdot l\cdot\big(\ln(2+l+q+n+m)\big)^{c}.$$
--   This is the sampling step of Algorithm 1.
--
--   Differences from the source:
--   - encoding: 'expected time', 'random access to the sparse representations of the rows of $A$' → expected log-cost `expCost` of one fixed program on the fair-coin log-cost RAM, input `matrixInput k l A` in memory; reason: the paper names no machine; a log-cost RAM with the input in memory gives random access to rows
--   - reading: expected time $\tilde O(l)$, $\tilde O$ suppressing factors polynomial in $\log(qnm)$ → $\le K\,l\,(\ln(2+l+q+n+m))^c$ with $K,c$ fixed before all parameters; reason: the paper's own $\tilde O$ convention for this lemma
--   - encoding: 'sampled exactly from $\nu(K_l(A))$' → the output is the sparse cells of $v$ with probability exactly $\nu(v)$ for every vertex $v$; reason: same law; when $K_l(A)$ has no edges $\nu$ is undefined and Lean's $\nu\equiv0$ asks for no vertex output
--   - encoding: $q$ a positive integer, $\mathbb Z_q^n$, indices $1,\dots,n$ → `[NeZero q]`, `Fin n → ZMod q`, indices `0, …, n−1`; reason: Lean convention; same instances
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 15, Lemma 4.1 (proof: App. A.1, pp. 45–46)

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Machine
import Definitions.Def_SmallSecretLWE_Classical_Kikuchi
import Definitions.Def_SmallSecretLWE_Classical_Encoding

open PrefixMixLearn.Proper (Program outProb)

namespace SmallSecretLWE.Classical

/-- Lemma 4.1. There are one fair-coin log-cost program and constants `K > 0`, `c` such that for
all `m, n, q, k, l` with `q ≥ 2`, `1 ≤ k ≤ n`, `⌈k/2⌉ ≤ l ≤ n`, and every `A ∈ Z_q^{m×n}` with
exactly `k` nonzero entries per row, run on the sparse rows of `A`: it outputs each vertex
`v ∈ (Z_q^n)_l` (as its sparse cells) with probability exactly `ν(v)`, the out-degree law of
`K_l(A)`, and its expected log-cost is at most `K · l · (log(2 + l + q + n + m))^c`. -/
theorem lemma_4_1 :
    ∃ (P : Program) (K : ℝ) (c : ℕ), 0 < K ∧
      ∀ (m n q k l : ℕ) [NeZero q], 2 ≤ q → 1 ≤ k → k ≤ n → (k + 1) / 2 ≤ l → l ≤ n →
      ∀ A : Matrix (Fin m) (Fin n) (ZMod q), HasKSparseRows k A →
        (∀ v : KVert n q l,
          outProb P nullOracle (matrixInput k l A) (fun o => o = sparseCells v.val) =
            (kikuchi A l).nu v) ∧
        expCost P nullOracle (matrixInput k l A) ≤
          ENNReal.ofReal (K * l * Real.log (2 + l + q + n + m) ^ c) := by sorry

end SmallSecretLWE.Classical
