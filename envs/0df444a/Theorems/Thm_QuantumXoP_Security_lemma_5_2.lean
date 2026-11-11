-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_5_2
-- name    : QuantumXoP.Security.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:32.4822+00:00
-- url     : https://prove2.me/theorems/478336a9-63e8-4105-acd0-fe6bd3b38fe5
-- title:
--   Lemma 5.2 — degree-wise weights of $\mu_{XoP[r]}$
-- statement:
--   Let $r\ge2$, $N=2^n\ge\max\{16r,96\}$ and $5\le d_{\max}\le N/28887$. Then:
--   1. $\mu^{=1}_{XoP[r]}=0$;
--   2. $\|\mu^{=2}_{XoP[r]}\|_2^2\le1/N^{2r-3}$;
--   3. $\|\mu^{=3}_{XoP[r]}\|_2^2\le O(1/N^{4r-5})$;
--   4. $\|\mu^{=4}_{XoP[r]}\|_2^2\le O(1/N^{4r-6})$;
--   5. $\|\mu^{=6}_{XoP[r]}\|_2^2\le O(1/N^{6r-9})$;
--   6. $\displaystyle\|\mu^{=5}_{XoP[r]}\|_2^2+\sum_{d=7}^{d_{\max}}\|\mu^{=d}_{XoP[r]}\|_2^2\le O(1/N^{6r-8})$;
--   7. in particular each of these terms is $O(1/N^{2r-3})$.
--
--   The constants hidden in $O(\cdot)$ depend only on $r$. Combined with Theorem 3.6 and the Cauchy–Schwarz inequality, item 7 gives Lemma 5.1.
--
--   **Formalization Note** One constant $C$ serves all $O(\cdot)$ clauses. Item 7 is stated for each $\|\mu^{=d}_{XoP[r]}\|_2^2$ with $d\in\{1,2,3,4,6\}$ and for the sum in item 6.
--
--   Differences from the source:
--   - reading: O(·), the hidden factor depending only on r (abstract; p. 14; p. 34) → ∃ C > 0, quantified after r and before n, q, the workspace, the algorithm and the output map; reason: the paper fixes what the hidden constant may depend on
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), pp. 14–15 (PDF pp. 16–17), Lemma 5.2

import Mathlib
import Definitions.Def_QuantumXoP_Security_Fourier

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 5.2 (pp. 14–15): for `r ≥ 2`, `N = 2^n ≥ max{16r, 96}` and `5 ≤ d_max ≤ N/28887`:
`μ^{=1}_{XoP[r]} = 0`; `‖μ^{=2}‖₂² ≤ 1/N^{2r−3}`; `‖μ^{=3}‖₂² ≤ O(1/N^{4r−5})`;
`‖μ^{=4}‖₂² ≤ O(1/N^{4r−6})`; `‖μ^{=6}‖₂² ≤ O(1/N^{6r−9})`;
`‖μ^{=5}‖₂² + Σ_{d=7}^{d_max} ‖μ^{=d}‖₂² ≤ O(1/N^{6r−8})`; and all of these terms are
`O(1/N^{2r−3})`. The hidden constant depends only on `r`. -/
theorem lemma_5_2 (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n dmax : ℕ, 16 * r ≤ 2 ^ n → 96 ≤ 2 ^ n → 5 ≤ dmax →
      28887 * dmax ≤ 2 ^ n →
      degComp (density (xopLaw n r)) 1 = 0 ∧
      l2norm (degComp (density (xopLaw n r)) 2) ^ 2 ≤ 1 / bigN n ^ (2 * r - 3) ∧
      l2norm (degComp (density (xopLaw n r)) 3) ^ 2 ≤ C / bigN n ^ (4 * r - 5) ∧
      l2norm (degComp (density (xopLaw n r)) 4) ^ 2 ≤ C / bigN n ^ (4 * r - 6) ∧
      l2norm (degComp (density (xopLaw n r)) 6) ^ 2 ≤ C / bigN n ^ (6 * r - 9) ∧
      l2norm (degComp (density (xopLaw n r)) 5) ^ 2 + ∑ d ∈ Finset.Icc 7 dmax, l2norm (degComp (density (xopLaw n r)) d) ^ 2 ≤
        C / bigN n ^ (6 * r - 8) ∧
      (∀ d ∈ ({1, 2, 3, 4, 6} : Finset ℕ), l2norm (degComp (density (xopLaw n r)) d) ^ 2 ≤ C / bigN n ^ (2 * r - 3)) ∧
      l2norm (degComp (density (xopLaw n r)) 5) ^ 2 + ∑ d ∈ Finset.Icc 7 dmax, l2norm (degComp (density (xopLaw n r)) d) ^ 2 ≤
        C / bigN n ^ (2 * r - 3) := by sorry

end QuantumXoP.Security
