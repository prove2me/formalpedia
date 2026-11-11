-- Prove2me | Theorems.Thm_QMultiMean_display_3
-- name    : QMultiMean.display_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:09:30.102754+00:00
-- url     : https://prove2.me/theorems/15f136b5-48be-4055-9cb7-8ba1edeea0a5
-- title:
--   Display (3) — $\mathbb E\|Y_j\|_2<2^{-(j-1)}$
-- statement:
--   Let $Y$ be a finite random variable over $\mathbb R^d$ and $Q$ the quantile function of $\|Y\|_2$. Let $j\ge0$ and $0\le a_{j-1}<a_j$, where $a_{j-1}=0$ if $j=0$ and $a_{j-1}\ge Q(2^{-(j-1)})$ if $j\ge1$. Then $Y_j=\frac1{a_j}[\![Y]\!]_{a_{j-1}}^{a_j}$ satisfies
--   $$\mathbb E[\|Y_j\|_2]<2^{-(j-1)} .$$
--
--   So $2^{-(j-1)}$ is a valid bound $L_2$ for the bounded estimator of Theorem 3.3 applied to the slice $Y_j$.
--
--   Differences from the source:
--   - generalization: Y = X − η, the centred variable of Algorithm 2 → any finite random variable Y over ℝ^d; reason: the display's argument uses only that Y is a finite random variable; X − η is one
--   - reading: Pr[‖Y‖₂ > a_{j−1}] ≤ Pr[‖Y‖₂ > Q(2^{−(j−1)})] for all j ∈ {0, …, k}, with a_{−1} = 0 → a_{j−1} = 0 when j = 0, and a_{j−1} ≥ Q(2^{−(j−1)}) when j ≥ 1; reason: at j = 0 the order 2 lies outside Definition 2.3's p ∈ [0, 1]; the algorithm sets a_{−1} = 0
--   - encoding: a_{j−1} = a_j handled by setting µ̃_j = 0 → a_{j−1} < a_j; reason: the truncation ⟦·⟧_a^b of p.6 is defined for 0 ≤ a < b, and Algorithm 2 skips a_{j−1} = a_j; 0 ≤ a_{j−1} follows from the quantile hypothesis (a quantile of ‖Y‖₂ is ≥ 0)
--   - encoding: a finite sample set Ω with 0 ∈ Ω → Ω = Fin (N+1) with distinguished point 0; reason: every finite pointed set is in bijection with some Fin (N+1); the estimator may depend on Ω anyway
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.12, proof of Theorem 3.4, display (3)

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_quantile

set_option autoImplicit false

namespace QMultiMean

/-- Display (3) in the proof of Theorem 3.4 of Cornelissen, Hamoudi, Jerbi, arXiv:2111.09787v2,
p.12: with `Y_j = (1/a_j)⟦Y⟧_{a_{j−1}}^{a_j}` (Algorithm 2, step 4b, `a_{−1} = 0`), since
`Pr[‖Y‖₂ > a_{j−1}] ≤ Pr[‖Y‖₂ > Q(2^{−(j−1)})] < 2^{−(j−1)}`, `E[‖Y_j‖₂] < 2^{−(j−1)}`.

**Formalization Note.** `a'` stands for `a_{j−1}` and `a` for `a_j`, with `a' < a` (the
truncation `⟦·⟧_{a'}^{a}` of p.6 is defined for `0 ≤ a' < a`; Algorithm 2 skips `a_{j−1} = a_j`). The
hypothesis on `a'` is `a' = 0` when `j = 0` (`a_{−1} = 0`) and `a' ≥ Q(2^{−(j−1)})` when `j ≥ 1`
(`Q` the quantile function of `‖Y‖₂`); either case gives `0 ≤ a'`, since a quantile of `‖Y‖₂` at an
order in `(0, 1]` is nonnegative. `2^{−(j−1)}` is written `2/2^j`. Stated for every finite
random variable `Y` over `ℝ^d` (in the proof, `Y = X − η`). -/
theorem display_3 (d N : ℕ) (P : Fin (N + 1) → ℝ) (Y : Fin (N + 1) → Vec d) (hP : IsPMF P)
    (j : ℕ) (a' a : ℝ) (haa : a' < a)
    (hj : (j = 0 ∧ a' = 0) ∨ (1 ≤ j ∧ quantile P (fun ω => ‖Y ω‖) (2 / 2 ^ j) ≤ a')) :
    expect P (fun ω => ‖(1 / a) • trunc a' a (Y ω)‖) < 2 / 2 ^ j := by sorry

end QMultiMean
