-- Prove2me | Theorems.Thm_PrivOptTest_eq_7
-- name    : PrivOptTest.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:21.597788+00:00
-- url     : https://prove2.me/theorems/99e269c9-5a09-4346-adc2-9189c3f39e5b
-- title:
--   Equation (7), p.15 — the hard inputs realize Greater-Than
-- statement:
--   Let $\mathcal X=\{x_1<\dots<x_m\}\subset\mathbb R$ with $m\ge3$, $\ell=\lfloor\log_2(m-2)\rfloor$, $t\le n$, and $i,j\in\{2,\dots,2^\ell+1\}$. With $S^{(i)}_A$ ($n-t$ copies of $x_1$, $t$ of $x_i$, labelled $-1$) and $S^{(j)}_B$ ($t$ copies of $x_j$, $n-t$ of $x_m$, labelled $+1$),
--   $$\mathrm{opt}_{\mathcal H_{\mathrm{thr}}}\big(S^{(i)}_A,S^{(j)}_B\big)=\begin{cases}0,&i<j,\\t,&i\ge j.\end{cases}$$
--
--   So a tester with resolution $t$ computes $\mathrm{GT}_\ell(i,j)=\mathbf 1\{i\ge j\}$.
--
--   Differences from the source:
--   - encoding: x_1 ≤ ⋯ ≤ x_m → the points of X in increasing order (strict since |X| = m); reason: same instances
--   - encoding: ℓ = ⌊log₂(m − 2)⌋ → Nat.log 2 (m − 2) with m ≥ 3; reason: defined exactly when m − 2 ≥ 1
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), proof of Theorem 3.1, (7), p.15

import Mathlib
import Definitions.Def_PrivOptTest_IsTester
import Definitions.Def_PrivOptTest_gtInput

namespace PrivOptTest

/-- **Equation (7)** (proof of Theorem 3.1, p.15). Let `X = {x_1 < ⋯ < x_m} ⊂ ℝ`, `ℓ = ⌊log₂(m − 2)⌋`
and `t ≤ n`. For `i, j ∈ {2, …, 2^ℓ + 1}`, with Alice holding `n − t` copies of `x_1` and `t` copies of
`x_i` (labelled −1) and Bob `t` copies of `x_j` and `n − t` copies of `x_m` (labelled +1),
`opt_{H_thr}(S^{(i)}_A, S^{(j)}_B) = 0` if `i < j` and `= t` if `i ≥ j`.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), proof of Theorem 3.1, (7), p.15.

**Formalization Note.** `m ≥ 3` so that `ℓ` is defined; `ℓ = Nat.log 2 (m − 2)`. The points are
`sortedPt X i`, 1-based. -/
theorem eq_7 (X : Finset ℝ) (hX : 3 ≤ X.card) (n t : ℕ) (htn : t ≤ n) (i j : ℕ)
    (hi : 2 ≤ i ∧ i ≤ 2 ^ Nat.log 2 (X.card - 2) + 1)
    (hj : 2 ≤ j ∧ j ≤ 2 ^ Nat.log 2 (X.card - 2) + 1) :
    opt Hthr (gtInputA X n t i) (gtInputB X n t j) = if i < j then 0 else t := by sorry

end PrivOptTest
