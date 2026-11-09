-- Prove2me | Theorems.Thm_Pr6453_recursion
-- name    : Pr6453.recursion
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T16:24:40.949695+00:00
-- url     : https://prove2.me/theorems/bcf0475e-6277-4e75-8b59-6c5de4245316
-- title:
--   PR #6453: the recursion composing the invoices into the $n(\lg n)^{1-\kappa}$ bound
-- statement:
--   The recursion of the PR #6453 word: the price inequality is exactly the statement that one level of the call tree costs a strictly smaller fraction of what the level above it produces, and consequently the whole tree costs at most a constant multiple of its root — with the same exponent $1-\kappa$ on the logarithm.
--
--   The first conjunct identifies the contraction ratio. At the claimed saving a call of the word produces $\sum_r T_r\,r^{1-\kappa}$ units and pays $\sum_r P_r\,r^{1-\kappa}$, and the price inequality says their ratio $\gamma$ is strictly below one.
--
--   The second conjunct is the geometric composition. If the cost of level $j+1$ is at most $\gamma$ times the cost of level $j$, then the sum over any number $L$ of levels is at most $C_0/(1-\gamma)$: the depth of the recursion costs a constant factor, not a factor that grows with the depth.
--
--   The third conjunct puts the logarithms back in. If the root costs at most $c\,n\,(\lg n)^{1-\kappa}$ then the whole tree costs at most $\dfrac{c}{1-\gamma}\,n\,(\lg n)^{1-\kappa}$, for every depth $L$. The exponent survives the recursion; only the constant is multiplied by $1/(1-\gamma)$, which is about $1.4\times10^{8}$ at the claimed saving — the numerical reason the source's claims are conditional.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: the moment criterion of research/p104-third-anchor-clean-mixed-root/pricing.py (margin k = moment T (1-k) - moment P (1-k), bisected, claimed saving below the root).

import Definitions.Def_Pr6453_RankMoments
import Definitions.Def_Pr6453_Recursion
import Definitions.Def_IntMul_MultitapeModel
import Theorems.Thm_Pr6453_moment_kappa_gt

set_option autoImplicit false

namespace Pr6453

theorem recursion :
    gamma < 1 ∧
      (∀ (C : ℕ → ℝ), 0 ≤ C 0 → (∀ j, C (j + 1) ≤ gamma * C j) →
        ∀ L : ℕ, (∑ j ∈ Finset.range L, C j) ≤ C 0 / (1 - gamma)) ∧
      (∀ (C : ℕ → ℝ) (c : ℝ) (n L : ℕ), 0 ≤ c → 0 ≤ C 0 →
        C 0 ≤ c * (n : ℝ) * ((IntMul.lg n : ℝ) ^ (1 - (kappa : ℝ))) →
        (∀ j, C (j + 1) ≤ gamma * C j) →
        (∑ j ∈ Finset.range L, C j) ≤
          (c / (1 - gamma)) * (n : ℝ) * ((IntMul.lg n : ℝ) ^ (1 - (kappa : ℝ)))) := by
  sorry

end Pr6453
