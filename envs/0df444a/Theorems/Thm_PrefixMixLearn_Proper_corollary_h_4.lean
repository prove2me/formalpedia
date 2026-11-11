-- Prove2me | Theorems.Thm_PrefixMixLearn_Proper_corollary_h_4
-- name    : PrefixMixLearn.Proper.corollary_h_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:46:24.002984+00:00
-- url     : https://prove2.me/theorems/9da31ad1-f961-4928-96f1-47b29005c31f
-- title:
--   Corollary H.4 (coefficient part; its resource clause is in theorem_3_1) — (1+θ)κ(α)^{-20} < 2^{321}α^{-100}
-- statement:
--   For rational $0<\alpha<1/2$ and $0<\theta\le1$, the complete learner's approximation coefficient satisfies
--   $$(1+\theta)\,\kappa(\alpha)^{-20}<2^{321}\alpha^{-100},$$
--   with $\kappa$ the ledger constant (H.1). This is polynomial dependence on the numerical value $1/\alpha$, not only on its encoding length. The corollary's other clause (a universal polynomial bounding every resource of the complete learner in $T,\alpha^{-1},\theta^{-1},\varepsilon^{-1},\log(1/\delta)$ and input length) is the resource clause of Theorem 3.1 (`theorem_3_1`).
--
--   Differences from the source:
--   - reading: there is a universal polynomial bounding the complete learner's ordinary bit time, target calls, returned symbols, written prefixes, learner bits, candidate count and output encoding length in T, α⁻¹, θ⁻¹, ε⁻¹, log(1/δ), total input length → stated in theorem_3_1 (one program, one exponent c, log-cost bound on every run); this item states the coefficient inequality; reason: 'the complete learner' is the program of Theorem 3.1; a free-standing ∃-program resource clause would be vacuous (a program that halts at once has polynomial resources), so the clause is carried by the goal
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 72 (PDF 74), Corollary H.4

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Ledger

namespace PrefixMixLearn.Proper

/-- Corollary H.4, the coefficient bound: for rational `0 < α < 1/2` and `0 < θ ≤ 1`, the
approximation coefficient of the complete learner satisfies `(1 + θ) κ^{-20} < 2^{321} α^{-100}`.
(The corollary's universal-polynomial resource clause for the complete learner is the resource
clause of `theorem_3_1`.) -/
theorem corollary_h_4 (α θ : ℚ) (hα0 : 0 < α) (hα1 : α < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (1 + (θ : ℝ)) * kappa α ^ (-20 : ℤ) < (2 : ℝ) ^ 321 * (α : ℝ) ^ (-100 : ℤ) := by sorry

end PrefixMixLearn.Proper
