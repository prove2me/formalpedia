-- Prove2me | Theorems.Thm_SLPricing_Resp_proposition_4
-- name    : SLPricing.Resp.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:10:24.727983+00:00
-- url     : https://prove2.me/theorems/e59fcbf3-afae-4cdb-8c61-9aec2f2008f0
-- title:
--   Proposition 4, p. 19 — without SL, the optimal responsive policy is $p_1^*=\frac{2c+\delta_c^2(1-c)+4(1-\delta_c)}{6-4\delta_c}$, $p_2^*=\frac{\chi(p_1^*)+c}{2}$
-- statement:
--   Consider responsive pricing without social learning ($\gamma=0$), with the closed forms $\chi$, $\pi_{br}$, $p_1^*$, $p_2^*$ of the benchmark definitions. For a consumer discount factor $d\in[0,1]$ in place of $\delta_c$:
--
--   1. $p_1^*$ is an optimal first-period price, the optimal expected profit $\pi^*_r$ equals $\pi_{br}(p_1^*)$, and some optimal equilibrium after $p_1^*$ charges the second-period price $p_2^*=\frac{\chi(p_1^*)+c}{2}$;
--   2. if $d<1$: every first-period price has a unique equilibrium set of first-period buyers, of the form $[\theta,1]$ up to a null set; $p_1^*$ is the only optimal first-period price; and every equilibrium after $p_1^*$ charges $p_2^*$ in period 2;
--   3. as functions of $d\in[0,1]$, $p_1^*$ is strictly decreasing, $p_2^*$ is strictly increasing, and the optimal profit $\pi_{br}(p_1^*)$ is strictly decreasing.
--
--   Explicitly, $\pi_{br}(p_1^*)=\frac{(1-c)^2(2-d)^2}{4(3-2d)}$. This is the no-learning benchmark value that Proposition 6 compares against.
--
--   **Formalization Note** Uniqueness (of the equilibrium and of the optimal price) is stated only for $d<1$. At $d=1$ every $p_1\ge(1+c)/2$ attains the optimal profit $(1-c)^2/4$, and equilibrium buyer sets are not unique (see the item for (5)). "Unique equilibrium" is formalized as uniqueness of the first-period buyer set up to null sets; uniqueness of the second-period price is Lemma 3. Monotonicity is strict, as the derivatives are nonzero on $[0,1)$.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Proposition 4, p. 19 (proof outline p. 31)

import Mathlib
import Definitions.Def_SLPricing_Resp_Model
import Definitions.Def_SLPricing_Resp_Benchmark
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Resp

/-- Proposition 4, p. 19 (proof outline p. 31): without social learning, for every consumer
discount factor `d ∈ [0, 1]`: `p∗₁` is an optimal first-period price, the optimal profit equals
`π_br(p∗₁)`, and an optimal equilibrium charges `p∗₂ = (χ(p∗₁) + c)/2` on the path. For `d < 1`
every first-period price has a unique equilibrium buyer set `[θ, 1]` (up to null sets), `p∗₁` is
the unique optimal first-period price and every equilibrium after `p∗₁` charges `p∗₂`.
Finally `p∗₁` is strictly decreasing, `p∗₂` strictly increasing and `π_br(p∗₁)` strictly
decreasing in `d ∈ [0, 1]`. -/
theorem proposition_4 (P : Params) (hP : P.Standing) :
    (∀ d ∈ Icc (0 : ℝ) 1,
      IsOptimalResp (P.withδc d).noSL (p1StarNoSL P.c d) ∧
      respValue (P.withδc d).noSL = ((profitNoSL P.c d (p1StarNoSL P.c d) : ℝ) : EReal) ∧
      (∃ B s, IsRespEq (P.withδc d).noSL (p1StarNoSL P.c d) B s ∧
        ((respProfit (P.withδc d).noSL (p1StarNoSL P.c d) B s : ℝ) : EReal) =
          respValue (P.withδc d).noSL ∧
        s 0 = p2StarNoSL P.c d)) ∧
    (∀ d ∈ Ico (0 : ℝ) 1,
      (∀ p₁ : ℝ, ∃ θ : ℝ, (∃ B s, IsRespEq (P.withδc d).noSL p₁ B s) ∧
        ∀ B s, IsRespEq (P.withδc d).noSL p₁ B s → B =ᵐ[volume] Icc θ 1) ∧
      (∀ p₁, IsOptimalResp (P.withδc d).noSL p₁ → p₁ = p1StarNoSL P.c d) ∧
      (∀ B s, IsRespEq (P.withδc d).noSL (p1StarNoSL P.c d) B s → s 0 = p2StarNoSL P.c d)) ∧
    StrictAntiOn (fun d => p1StarNoSL P.c d) (Icc 0 1) ∧
    StrictMonoOn (fun d => p2StarNoSL P.c d) (Icc 0 1) ∧
    StrictAntiOn (fun d => profitNoSL P.c d (p1StarNoSL P.c d)) (Icc 0 1) := by sorry

end SLPricing.Resp
