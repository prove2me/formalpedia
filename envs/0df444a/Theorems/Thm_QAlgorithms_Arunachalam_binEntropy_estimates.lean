-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_binEntropy_estimates
-- name    : QAlgorithms.Arunachalam.binEntropy_estimates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:08.100091+00:00
-- url     : https://prove2.me/theorems/f6860ffa-f428-4161-9c9f-4e7b6a95db32
-- title:
--   Binary entropy: H(ε) = O(ε log 1/ε) and 1 − H(1/2+ε) ≤ 2ε²/ln 2 + O(ε⁴)
-- statement:
--   Let $H(p)=-p\log_2p-(1-p)\log_2(1-p)$ be the binary entropy in bits. There are constants $C_1,C_2>0$ such that for all $\varepsilon\in[0,1/2]$:
--
--   1. $H(\varepsilon)\le C_1\,\varepsilon\log_2(1/\varepsilon)$;
--   2. $$
--   1-H(1/2+\varepsilon)\le\frac{2\varepsilon^2}{\ln 2}+C_2\,\varepsilon^4.
--   $$
--
--   These estimates convert entropy bounds into the $1/\varepsilon$ and $1/\varepsilon^2$ dependence of the information-theoretic sample complexity lower bounds.
--
--   **Formalization Note** The constants are chosen once, uniformly over $\varepsilon\in[0,1/2]$, as the source's "for all $\varepsilon\in[0,1/2]$" requires. At $\varepsilon=0$ Lean's $\log 0=0$ makes the first right side $0$, which equals $H(0)=0$.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 162, Fact 7.3.7. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_BooleanFourier
set_option autoImplicit false

namespace QAlgorithms.Arunachalam




/-- Arunachalam p.162, Fact 7.3.7: for all `ε ∈ [0, 1/2]`, `H(ε) ≤ O(ε log(1/ε))` and
`1 − H(1/2 + ε) ≤ 2ε²/ln 2 + O(ε⁴)`, where `H` is the binary entropy in bits and `log` is base 2.
The constants of both `O`'s are uniform over `ε ∈ [0, 1/2]`. -/
theorem binEntropy_estimates :
    (∃ C₁ : ℝ, 0 < C₁ ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 2 →
        binEntropy2 ε ≤ C₁ * (ε * Real.logb 2 (1 / ε))) ∧
      ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 2 →
        1 - binEntropy2 (1 / 2 + ε) ≤ 2 * ε ^ 2 / Real.log 2 + C₂ * ε ^ 4 := by
  sorry



end QAlgorithms.Arunachalam
