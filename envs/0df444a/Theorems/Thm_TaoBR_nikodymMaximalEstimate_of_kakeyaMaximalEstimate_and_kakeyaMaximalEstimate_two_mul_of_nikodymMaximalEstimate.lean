-- Prove2me | Theorems.Thm_TaoBR_nikodymMaximalEstimate_of_kakeyaMaximalEstimate_and_kakeyaMaximalEstimate_two_mul_of_nikodymMaximalEstimate
-- name    : TaoBR.nikodymMaximalEstimate_of_kakeyaMaximalEstimate_and_kakeyaMaximalEstimate_two_mul_of_nikodymMaximalEstimate
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:16:59.031005+00:00
-- url     : https://prove2.me/theorems/1e5d03c3-f041-4b73-8279-f54b0c7a70a9
-- title:
--   Theorem 4.10 — K(p, α) ⟹ N(p, α) ⟹ K(p, 2α) for 1 ≤ p ≤ n and 0 ≤ α < (n+1)/p
-- statement:
--   For $n \ge 2$, $1 \le p \le n$ and $0 \le \alpha < (n+1)/p$:
--   - the Kakeya maximal estimate $K(p, \alpha)$ implies the Nikodym maximal estimate $N(p, \alpha)$;
--   - $N(p, \alpha)$ implies $K(p, 2\alpha)$.
--
--   Here $K(p, \alpha)$ and $N(p, \alpha)$ are the bounds $\|f^*_\delta\|_{L^p(S^{n-1})}, \|f^{**}_\delta\|_p \lesssim \delta^{1 - n/p - \alpha}\|f\|_p$ of Conjectures 4.5 and 4.7, with the exponent corrected there.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 11, Theorem 4.10

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem nikodymMaximalEstimate_of_kakeyaMaximalEstimate_and_kakeyaMaximalEstimate_two_mul_of_nikodymMaximalEstimate
    (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp1 : 1 ≤ p) (hpn : p ≤ n) (α : ℝ) (hα : 0 ≤ α)
    (hα' : α < ((n : ℝ) + 1) / p) :
    (KakeyaMaximalEstimate n p α → NikodymMaximalEstimate n p α) ∧
    (NikodymMaximalEstimate n p α → KakeyaMaximalEstimate n p (2 * α)) := by
  sorry

end TaoBR
