-- Prove2me | Theorems.Thm_PrivRobustStat_lemma_1
-- name    : PrivRobustStat.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:11.032202+00:00
-- url     : https://prove2.me/theorems/f02f24b3-a19c-433c-926c-fab97300216d
-- title:
--   Lemma 1, p.11 — $\operatorname{Tr}(A_k^{2k-1})\le\operatorname{Tr}(A_1\cdots A_{k-1}A_kA_{k-1}\cdots A_1)$ for $A_1\succeq\cdots\succeq A_k\succeq0$
-- statement:
--   **Lemma 1** (multi-matrix trace inequality). Let $k\ge1$ and let $A_1,\dots,A_k$ be positive semidefinite $d\times d$ matrices with $A_1\succeq A_2\succeq\cdots\succeq A_k$. Then
--
--   $$\operatorname{Tr}\big(A_k^{2k-1}\big)\le\operatorname{Tr}\big(A_1A_2\cdots A_{k-1}A_kA_{k-1}\cdots A_2A_1\big).$$
--
--   It generalizes [JLT20, Lemma 7], the case $A_1=\cdots=A_{k-1}$, and gives the lower bound comparison in the potential argument (Lemma 12).
--
--   Differences from the source:
--   - encoding: A[k] = {A₁, …, A_k}, k ∈ ℕ → a family A : ℕ → Matrix with the paper's 1-based indices and k ≥ 1; reason: only A₁, …, A_k enter; [k] must contain k
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Lemma 1, p.11 (PDF p.14); proof in Appendix A.1, p.73

import Mathlib
import Definitions.Def_PrivRobustStat_Model

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Lemma 1** (multi-matrix trace inequality), p.11 (PDF p.14); proof in Appendix A.1, p.73.

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Let k ∈ N, and let A[k] ⊂ S^{d×d}_{⪰0} satisfy A₁ ⪰ A₂ ⪰ … ⪰ A_k. Then,
Tr(A_k^{2k−1}) ≤ Tr(A₁A₂ … A_{k−1}A_kA_{k−1} … A₂A₁)."

**Formalization Note.** The family is indexed by `ℕ` with the paper's 1-based indices; only
`A 1, …, A k` enter. `k ≥ 1` (the paper's `[k] = {1, …, k}` must contain `k`). PSD is
`Matrix.PosSemidef` (symmetric with nonnegative quadratic form); `A_i ⪰ A_j` is
`(A i − A j).PosSemidef`. The palindromic product is the product of the list
`[A₁, …, A_k] ++ [A_{k−1}, …, A₁]`. -/
theorem lemma_1 {d : ℕ} (k : ℕ) (hk : 1 ≤ k) (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hpsd : ∀ i ∈ Finset.Icc 1 k, (A i).PosSemidef)
    (hord : ∀ i ∈ Finset.Icc 1 k, ∀ j ∈ Finset.Icc 1 k, i ≤ j → (A i - A j).PosSemidef) :
    Matrix.trace (A k ^ (2 * k - 1)) ≤
      Matrix.trace (((List.range k).map (fun i => A (i + 1)) ++
        ((List.range (k - 1)).map (fun i => A (i + 1))).reverse).prod) := by sorry

end PrivRobustStat
