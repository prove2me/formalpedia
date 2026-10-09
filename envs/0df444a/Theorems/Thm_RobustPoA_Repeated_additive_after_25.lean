-- Prove2me | Theorems.Thm_RobustPoA_Repeated_additive_after_25
-- name    : RobustPoA.Repeated.additive_after_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:50.515683+00:00
-- url     : https://prove2.me/theorems/f8cef4e3-ad4d-465d-a369-81558727998c
-- title:
--   §3.2, p. 14, after (25) — robust-POA bound with vanishing additive error
-- statement:
--   Let $G$ have a nonnegative joint cost $C$, at least one admissible smoothness pair with $\mu<1$, and an outcome sequence $s^1,s^2,\ldots$ with vanishing average external regret for every player. For every comparison outcome $s'$, there is a sequence $\eta(T)\to0$ such that, for every $T\geq1$,
--
--   $$\frac1T\sum_{t=1}^{T}C(s^t)\leq\rho(G)C(s')+\eta(T).$$
--
--   This is the additive conclusion drawn immediately after equation (25). It remains meaningful when the comparison cost is zero.
--
--   **Formalization Note** The paper phrases the conclusion for an optimal outcome. The same derivation applies to every comparison outcome. The nonnegative objective is the paper's standing convention. $\rho(G)$ is the extended-real infimum; the admissible-pair hypothesis makes it less than $+\infty$ (it is a real number at least 1 when some outcome has positive cost, and the bound reads $0\le\eta(T)$ when every outcome costs zero). The comparison is made in the extended reals, where both sides are finite.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), paragraph after (25), §3.2, p. 14

import Mathlib
import Definitions.Def_RobustPoA_Static_Smoothness
import Definitions.Def_RobustPoA_Repeated_Regret

namespace RobustPoA.Repeated

/-- The additive conclusion stated in the paragraph following equation (25). -/
theorem additive_after_25 {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ)
    (hC : ∀ s, 0 ≤ RobustPoA.Static.cost C s)
    (hsmooth : ∃ lam mu : ℝ, mu < 1 ∧ RobustPoA.Static.IsSmooth C lam mu)
    (seq : ℕ → ∀ i, S i) (hreg : VanishingRegret C seq)
    (s' : ∀ i, S i) :
    ∃ η : ℕ → ℝ, Filter.Tendsto η Filter.atTop (nhds 0) ∧
      ∀ T : ℕ, 1 ≤ T →
        (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, RobustPoA.Static.cost C (seq t) ≤
          RobustPoA.Static.robustPoA C * RobustPoA.Static.cost C s' + η T := by sorry

end RobustPoA.Repeated
