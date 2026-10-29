-- Prove2me | Theorems.Thm_RefDemandLearning_SlowMoving_theorem_3
-- name    : RefDemandLearning.SlowMoving.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:25:01.319991+00:00
-- url     : https://prove2.me/theorems/d9d3852c-a1a9-4e68-ae1e-bf9c73c1408a
-- title:
--   Theorem 3 — asymptotic optimality of the slow-moving pricing policy
-- statement:
--   Fix a price interval $[\ell,u]$ with $0\le\ell<u$ and the known parameter rectangle of Section 2. Its loss-averse subset $\Theta$ has $\alpha\ge0$, $\beta>0$, $0\le\eta^+\le\eta^-$, nonnegative expected demand throughout the box, and $\ell<\alpha/(2\beta)<u$ for every parameter vector in $\Theta$. Demand is $d(p,r,\theta)=\alpha-\beta p+\eta^+(r-p)^+-\eta^-(p-r)^+$ and revenue is $R=p d$.
--
--   Use the actual policy $S$ with $n_i=2^i$, $\delta_i=c_0 2^{-i/4}$, $0<c_0<2^{-3/4}(u-\ell)$, and initial estimates in the known intercept and slope intervals. Its clipped two-price experiments and projected least-squares updates use only the latest complete episode's observations. On any probability space, the shocks are measurable iid real variables of mean zero, finite variance, and a finite MGF in some neighborhood of zero. The law is unknown to the policy. Regret is the full dynamic clairvoyant supremum minus expected cumulative revenue of this causal run.
--
--   Fix $\theta\in\Theta$ and a full infinite mechanism $\rho\in\mathcal R_G$. Thus there are change times $\tau_1=1$, strictly increasing while finite, possibly infinitely many, and coefficients $\zeta_k\in[0,1)$. Reference maps are continuous and interval-valued; between changes $r_{t+1}=\zeta_k r_t+(1-\zeta_k)p_t$, and at changes the reference can reset based on the entire price history. One finite $c>0$ bounds the number of change times in every interval $(s,t]$, $1\le s<t$, by $c\sqrt{t-s}$. No uniform upper bound below one is imposed on $\zeta_k$.
--
--   There exists a finite $c_6>0$, depending on these fixed data but independent of the horizon, such that
--   $$\Delta_S(T,\rho,\theta)\le c_6\sqrt T\qquad\text{for every integer }T\ge1.$$
--   This is the full printed Theorem 3, including all positive horizons and incomplete episode prefixes. Neither of Proposition 2's sufficient bounds is an assumption of this theorem. The source links $c_6$ to Proposition 2; its existential, horizon-independent meaning is retained. The recorded gap in the source's proof does not alter this target.
--
--   **Formalization Note.** Continuous resets and infinitely many changes are represented directly. Change times use extended naturals; the transition condition avoids subtracting from infinity. The explicit expression for the proof's $c_6$ is documented in the moderation notes rather than made an additional premise.
--
--   Differences from the source:
--   - encoding: periods start at 1 and positive integer horizons → period n represents source period n+1; horizons and interval endpoints retain explicit positive-natural guards; reason: finite histories use Fin n and finite sums are reindexed without changing any term
--   - encoding: episodewise unconstrained least-squares argmin and subsequent componentwise projection → the unique two-block least-squares formula with the same coordinate projections and interval-valued prices in a causal prefix recursion; reason: both blocks have equal positive length and distinct prices; only the most recent complete episode is used; the center is interior under the standing assumptions, so full interval clipping equals the printed one-sided clipping
--   - generalization: policy histories in (2.5) have nonnegative demand coordinates → the same policy rule is defined for all real observations; reason: the additive-noise model permits negative realizations; the extension agrees on every nonnegative history and does not truncate demand
--   - encoding: dynamic finite-horizon supremum and expected cumulative revenue → a real supremum over the whole compact price box and a Bochner integral on a probability space; reason: the concrete Borel causal recursion has bounded finite-horizon revenues, so the integral and supremum are the ordinary finite values
--   - encoding: change times in positive naturals with infinity and the double indicator sum in (3.6) → WithTop naturals with zero-based regime indices, counting distinct finite change times, and transitions using t+1 less than the next change; reason: finite change times are strictly increasing, so the counts agree; no subtraction from infinity or finite-regime restriction is introduced
--   - encoding: c6 is as given in Proposition 2 → existence of a positive real c6 before the universal horizon; reason: Proposition 2 asserts a finite positive horizon-independent constant; no additional c4 or c5 condition is assumed in the goal
-- source:
--   den Boer and Keskin, Dynamic Pricing with Demand Learning and Reference Effects, DOI https://doi.org/10.1287/mnsc.2021.4234, supplied April 19, 2021 artifact, Theorem 3, printed p. 17, PDF p. 17

import Definitions.Def_RefDemandLearning_SlowMoving_Mechanism
import Definitions.Def_RefDemandLearning_SlowMoving_Model
import Definitions.Def_RefDemandLearning_SlowMoving_Noise
import Definitions.Def_RefDemandLearning_SlowMoving_Policy
import Definitions.Def_RefDemandLearning_SlowMoving_Regret

set_option autoImplicit false
open MeasureTheory

namespace RefDemandLearning.SlowMoving

theorem theorem_3 (B : Bounds) (hB : Standing B) (ρ : Mechanism B.prices)
    (hρ : IsGeneral ρ) (θ : Parameters) (hθ : InTheta B θ)
    (c₀ a₀ b₀ : ℝ) (hpolicyTuning : TuningOK B c₀ a₀ b₀)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (hnoise : AdmissibleNoise P ε) :
    ∃ c₆ : ℝ, 0 < c₆ ∧ ∀ T : ℕ, 1 ≤ T →
      regret B ρ θ c₀ a₀ b₀ P ε T ≤ c₆ * Real.sqrt T := by sorry

end RefDemandLearning.SlowMoving
