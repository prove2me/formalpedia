-- Prove2me | Theorems.Thm_WernerExt_TwoSided_casimir_dominance
-- name    : WernerExt.TwoSided.casimir_dominance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:24.682588+00:00
-- url     : https://prove2.me/theorems/dd9673e6-375e-425d-af03-22c2844fd431
-- title:
--   Eq. (10), p. 3 (corrected: c(λ) − c(μ) = 2[(k − i) + (μ_i − μ_k) + 1], not (k − i) + (μ_i − μ_k)) — a dominance cover raises c by at least 1; c refines dominance order
-- statement:
--   Let $d\ge2$ and $n\ge0$; all partitions below are $d$-partitions of $n$, and $c$ is Eq. (9).
--
--   1. If $\lambda$ covers $\mu$ in dominance order, then $c(\lambda)-c(\mu)\ge1$.
--   2. The order of the Casimir eigenvalues refines dominance order: if $\lambda\trianglerighteq\mu$ and $\lambda\ne\mu$, then $c(\lambda)>c(\mu)$.
--   3. If $\lambda$ is obtained from $\mu$ by removing one box from row $k$ and appending it to row $i<k$, then $$c(\lambda)-c(\mu)=2\left[(k-i)+(\mu_i-\mu_k)+1\right].$$
--
--   These facts show that a dominance-minimal constituent has the smallest Casimir eigenvalue.
--
--   **Formalization Note** Clause 3 is stated for every such box move between $d$-partitions; a cover in dominance order is a box move of this kind (p. 3).
--
--   Differences from the source:
--   - correction: the middle equalities of (10): c(λ) − c(μ) = (k − i) + (λ_i − λ_k) − 2 = (k − i) + (μ_i − μ_k) → c(λ) − c(μ) = 2[(k − i) + (μ_i − μ_k) + 1]; reason: the printed value is false: for d = 2, λ = (2, 0) covers μ = (1, 1) (box from row k = 2 to row i = 1), c(λ) = 4 and c(μ) = 0, so c(λ) − c(μ) = 4 while (k − i) + (μ_i − μ_k) = 1; the corrected formula is checked on all 560 box moves with d ≤ 5 and rows ≤ 4
--   - generalization: clause 3 under the hypothesis that λ covers μ → clause 3 for every move of one box from row k to row i < k between d-partitions of n; reason: the computation does not use the cover property; covers are such moves, so it specializes to the source
--   - encoding: λ ⊢ n, μ ⊢ n arbitrary partitions → d-partitions of n; reason: c is defined for d-row diagrams (Eq. (9)), and every partition dominating a d-row partition has at most d rows, so covers among d-partitions are covers among all partitions
--   - encoding: 1-based rows λ_1, …, λ_d and sites → 0-based `Fin d` rows and `Fin n` sites; reason: Lean indexing convention; same instances
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, p. 3, Eq. (10) and the cover paragraph after Eq. (7)

import Mathlib
import Definitions.Def_WernerExt_TwoSided_Model

namespace WernerExt.TwoSided

/-- Eq. (10), p. 3: (a) if `λ` covers `μ` in dominance order (both `d`-partitions of `n`), then
`c(λ) − c(μ) ≥ 1`; (b) the order of the Casimir eigenvalues refines dominance order:
`λ ⊵ μ`, `λ ≠ μ` implies `c(λ) > c(μ)`; (c) (corrected middle equalities of (10)) if `λ` is
obtained from `μ` by moving one box from row `k` to row `i < k`, then
`c(λ) − c(μ) = 2[(k − i) + (μ_i − μ_k) + 1]`. -/
theorem casimir_dominance (d n : ℕ) (hd : 2 ≤ d) :
    (∀ l m : DPart d n, Covers l m → casimirValue m.1 + 1 ≤ casimirValue l.1) ∧
      (∀ l m : DPart d n, Dominates l.1 m.1 → l ≠ m → casimirValue m.1 < casimirValue l.1) ∧
      (∀ (l m : DPart d n) (i k : Fin d), i < k → l.1 i = m.1 i + 1 → l.1 k + 1 = m.1 k →
        (∀ r : Fin d, r ≠ i → r ≠ k → l.1 r = m.1 r) →
        casimirValue l.1 - casimirValue m.1 =
          2 * (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ) + ((m.1 i : ℝ) - (m.1 k : ℝ)) + 1)) := by sorry

end WernerExt.TwoSided
