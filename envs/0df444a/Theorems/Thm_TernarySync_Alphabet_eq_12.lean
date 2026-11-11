-- Prove2me | Theorems.Thm_TernarySync_Alphabet_eq_12
-- name    : TernarySync.Alphabet.eq_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:54:19.460774+00:00
-- url     : https://prove2.me/theorems/7118d65b-c0ef-4e56-8c71-cacc3fd5d769
-- title:
--   Eq. (12) — ternary deletion ball: $|B_\ell(y)| \le \exp[\eta\ell(\log 2 + 2\log(e/\eta) + \log 3)] < e^{9\ell/500}$
-- statement:
--   Let $\eta = 1/1000$ and let $\ell$ be an integer with $\eta\ell > 1$. For every ternary word $y \in \{0,1,2\}^\ell$, the deletion ball $B_\ell(y) = \{x \in \{0,1,2\}^\ell : \mathrm{LCS}(x,y) > (1-\eta)\ell\}$ satisfies
--
--   $$|B_\ell(y)| \le \exp\!\big[\eta\ell\,\big(\log 2 + 2\log(e/\eta) + \log 3\big)\big] < e^{9\ell/500}. \tag{12}$$
--
--   So the number of near matches of a fixed neighbour grows at rate at most $9/500$ per symbol, below the source's decay rate $(\log 2)/18$; this gap is what makes the ternary construction work.
--
--   **Formalization Note.** $\log$ is the natural logarithm (`Real.log`) and $e = $ `Real.exp 1`; $|B_\ell(y)|$ is `Set.ncard` of `delBall (1/1000) ℓ y`.
--
--   Differences from the source:
--   - encoding: the ternary case, ηℓ > 1, a fixed neighbour y of length ℓ → y : List (Fin 3) with y.length = ℓ, hypothesis 1 < ℓ/1000; reason: the setting of the sentence written as binders
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 16 (PDF 17), §4, Eq. (12)

import Mathlib
import Definitions.Def_TernarySync_Alphabet_RandomSource

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Equation (12) (p. 16): in the ternary case, with `η = 1/1000` and `ηℓ > 1`, for every word
`y` of length `ℓ` over `{0, 1, 2}`,
`|B_ℓ(y)| ≤ exp[ηℓ(log 2 + 2 log(e/η) + log 3)] < e^{9ℓ/500}`. -/
theorem eq_12 (ℓ : ℕ) (hℓ : 1 < (1 : ℝ) / 1000 * (ℓ : ℝ)) (y : List (Fin 3))
    (hy : y.length = ℓ) :
    ((delBall ((1 : ℝ) / 1000) ℓ y).ncard : ℝ) ≤
        Real.exp ((1 : ℝ) / 1000 * (ℓ : ℝ) *
          (Real.log 2 + 2 * Real.log (Real.exp 1 / ((1 : ℝ) / 1000)) + Real.log 3)) ∧
      Real.exp ((1 : ℝ) / 1000 * (ℓ : ℝ) *
          (Real.log 2 + 2 * Real.log (Real.exp 1 / ((1 : ℝ) / 1000)) + Real.log 3)) <
        Real.exp (9 * (ℓ : ℝ) / 500) := by sorry

end TernarySync.Alphabet
