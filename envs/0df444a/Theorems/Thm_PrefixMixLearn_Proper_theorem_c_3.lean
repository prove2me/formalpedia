-- Prove2me | Theorems.Thm_PrefixMixLearn_Proper_theorem_c_3
-- name    : PrefixMixLearn.Proper.theorem_c_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:45:32.07036+00:00
-- url     : https://prove2.me/theorems/8a246a82-7b7c-4ca8-ab15-f87b10fc2200
-- title:
--   Theorem C.3 — linear control of next-bit conditional means on a typical trajectory
-- statement:
--   Let $T\ge1$, $0<\alpha<1/2$, and let $P,M$ be full-support laws on $\{0,1\}^T$ with $M(1\mid h)\in[\alpha,1-\alpha]$ for every proper prefix $h$. Write $p_i(x)=P(1\mid x_{<i})$, $m_i(x)=M(1\mid x_{<i})$ and $\eta=d_{TV}(P,M)$. If $\eta\le1/32$, then
--   $$M\Big[\sum_{i=1}^T(p_i(X)-m_i(X))^2\le\frac{1024}{\alpha}\eta^2\Big]\ge\frac34,$$
--   and the same event has probability at least $3/4-\eta$ under $P$. The constants depend neither on $T$ nor on a separation. This is the trajectory control that the signed unmixing of Appendix D builds on.
--
--   Differences from the source:
--   - encoding: M(1 | h) ∈ [α, 1 − α] for every proper prefix h → ∀ x i, α ≤ condOne M x i ≤ 1 − α; reason: every proper prefix is x_{<i} for some x and i, and condOne M x i = M(1 | x_{<i})
--   - encoding: coordinates i = 1, …, T; laws on {0,1}^T → `Fin T`, coordinate i ↦ i.val + 1; laws are real functions on `Fin T → Bool` with `IsLaw`; reason: Lean convention; same statement
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 23 (PDF 25), Theorem C.3

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws

namespace PrefixMixLearn.Proper

/-- Theorem C.3 (linear control on a typical trajectory): for full-support laws `P, M` on
`{0,1}^T` with every next-bit mean `M(1 | h)` in `[α, 1 − α]`, if `η = d_TV(P, M) ≤ 1/32` then the
event `Σ_i (p_i(X) − m_i(X))² ≤ (1024/α) η²` has `M`-probability at least `3/4` and
`P`-probability at least `3/4 − η`. -/
theorem theorem_c_3 (T : ℕ) (hT : 1 ≤ T) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 / 2)
    (P M : Cube T → ℝ) (hP : IsLaw P) (hPf : FullSupport P) (hM : IsLaw M)
    (hMf : FullSupport M)
    (hMbal : ∀ (x : Cube T) (i : Fin T), α ≤ condOne M x i ∧ condOne M x i ≤ 1 - α)
    (hη : tv P M ≤ 1 / 32) :
    3 / 4 ≤ massOf M {x | ∑ i, (condOne P x i - condOne M x i) ^ 2 ≤ 1024 / α * tv P M ^ 2} ∧
      3 / 4 - tv P M ≤
        massOf P {x | ∑ i, (condOne P x i - condOne M x i) ^ 2 ≤ 1024 / α * tv P M ^ 2} := by sorry

end PrefixMixLearn.Proper
