-- Prove2me | Theorems.Thm_RetirePartialInfo_Duality_Supplement_theorem_3_3
-- name    : RetirePartialInfo.Duality.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:24:24.448518+00:00
-- url     : https://prove2.me/theorems/3c62550b-bdc5-46f0-b4b2-386ab1b9cb76
-- title:
--   Theorem 3.3 (corrected verification reading) — inverse multiplier and optimal consumption, bequest and retirement
-- statement:
--   Fix the two-state hidden-drift market with $\mu_1>\mu_2$, positive switching rates, and CRRA parameter $\gamma>0$, $\gamma\ne1$. Let $v,f$ be the supplied post-retirement PDE and bounded retirement VI solutions in the local strong-solution classes specified in the definition layer. No optimal stopping time, inverse multiplier, budget equality or derivative sign is assumed.
--
--   For every $t\in[0,T]$, $p\in(0,1)$ and $x>b(t)$, the increasing dual marginal has a unique positive root at $b(t)-x$. With
--
--   $$y^*=I_{\widehat v}(t,b(t)-x,p),\quad y_s^*=y^*e^{\beta(s-t)}\frac{B_t\mathcal Z_s}{B_s\mathcal Z_t},\quad \tau^*=\inf\{s\in[t,T_1]:y_s^*\le\Xi(s,p_s)\}\wedge T_1,$$
--
--   the multiplier $y^*$ is positive, $\partial_y\widehat v(t,y^*,p)=b(t)-x$, $\tau^*$ is an observation stopping time and its candidate budget cost equals $x-b(t)$. The controls
--
--   $$H_T^*=I_2(T,y_T^*),\qquad c_s^*=I_1(s,y_s^*),\qquad R_s^*=\mathbf1_{\{s\ge\tau^*\}}$$
--
--   admit a feasible adapted wealth process and attain the greatest objective among all observation-adapted budget-feasible plans from initial wealth $x$. The PDE functions agree with the actual restarted dual expectations/stopping values, including the retired branch after $T_1$. At time zero the restarted feasible set, objective and dual values coincide with the immutable base definitions.
--
--   **Formalization Note** The threshold is the extended supremum of the actual contact set, covering zero income, empty contact and terminal contact. The supplied functions use local verification regularity; the false global existence claims are refuted in companion milestones. The growth bound is repaired to $C(1+y^k+y^{-k})$, as supported by Appendix A's homogeneous formula. Finite integrability and strict consumption/bequest positivity use the published base conventions. The HMM law is restarted in elapsed time; this does not freeze belief or change the observation filtration.
--
--   Differences from the source:
--   - correction: One-sided growth (31) in the PDE verification context → Explicit two-sided polynomial bound on the supplied post-retirement solution; reason: Appendix A gives v=-y^φ w/φ, so v_p grows at infinity for γ>1 when w_p is nonzero; bounded w and w_p support the displayed replacement without excluding any source CRRA regime
--   - reading: Functions defined in Propositions 3.1–3.2 → Supplied PDE/VI solutions with explicit local strong-solution regularity, without assuming their derivative signs or stopping geometry; reason: This is the verification antecedent of Theorem 3.3; source global existence claims are false and are addressed independently, not used as vacuous premises
--   - encoding: Finite max of contact log y and boundary hitting time → Extended positive-y contact supremum and capped nonempty infimum; reason: The finite max is undefined at ξ=0. At the mandatory date the full contact supremum is ∞, whereas Proposition 3.3 assigns the finite left limit ℓ/ξ when ξ>0; the mandatory cap makes either terminal value give the same hitting time
--   - encoding: Conditional problem at calendar time t → Initial-state HMM law restarted at elapsed zero and the full density ratio; reason: This realizes every current-time/interior-belief state without conditioning on a zero-probability event and keeps the wealth shift and all budget intervals
--   - generalization: Displayed optimal strategies of Theorem 3.3 → Also concludes the verification identities with restarted dual values and exact compatibility with base time-zero objects; reason: These encode the identifications of Propositions 3.1–3.2 and establish that the general-time choice problem extends the frozen mission
--   - generalization: Current time t ∈ [0,T) of the proof on p.25 → t ∈ [0,T], including the retired range t > T1 and the degenerate end t = T; reason: For t > T1, b(t)=0, v̂=ṽ and the source's τ* = inf ∅ ∧ T1 = T1 < t gives R* ≡ 1 on [t,T]; the Lean hit time is elapsed 0, the same plan. At t = T the plan is H = x and the claim holds trivially
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), pp. 24–26, Theorem 3.3; pp. 17–19, Propositions 3.1–3.2; pp. 35–39, Appendices A–D

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Supplement_Verification

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

namespace RetirePartialInfo.Duality.Supplement

/-- Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553
(version of June 8, 2021), pp.24–26, Theorem 3.3, using (27)–(33), pp.16–17.
**Formalization Note.** General current time, full interior belief, and both CRRA regimes.
The supplied PDE/VI functions have the local strong-solution regularity used in verification,
not the false global membership printed in Theorems 3.1–3.2. Appendix A supports two-sided
polynomial growth, replacing (31)'s bound which is incompatible with γ>1 at large y.
The inverse multiplier, budget matching, observation stopping-time property and primal
attainment are conclusions. The extended contact threshold covers ξ=0 and t=T1 without
an artificial finite maximum. Integrability/positivity in the primal is the published base
convention. Initial wealth is x; its augmented budget is x-b(t).
The identifications with L are conclusions, not definitions of the PDE solutions.
The strategy clause covers every current time t ∈ [0,T] (the proof on p.25 works on [0,T)).
For t > T1 the agent is already retired: b(t)=0, v̂=ṽ, and the source's τ* = inf ∅ ∧ T1 = T1 < t
gives R* ≡ 1 on [t,T]; the elapsed-time `hit` is 0, the same plan. t = T is the degenerate end. -/
theorem theorem_3_3 {Sample : Type} [MeasurableSpace Sample]
    (a : Data) (ha : a.Admissible) (m : HMMFamily Sample) (hm : m.Standing a)
    (v f : Value) (hv : PostSolution a v) (hf : ObstacleSolution a f) :
    (∀ p ∈ Ioo (0 : ℝ) 1, ∀ x : ℝ, ∀ q : Plan Sample,
      (feasible a m 0 p x q ↔ q ∈ Bclass a.par (m.market 0 p) (m.integralTheta 0 p)
        (crra a) (crra a) x) ∧
      objective a m 0 p q = J a.par (m.market 0 p) (crra a) (crra a) q) ∧
    (∀ p ∈ Ioo (0 : ℝ) 1, ∀ y > 0,
      restartedL1 a m 0 y p = L1 a.par (m.market 0 p) (m.density 0 p) (crra a) (crra a) y ∧
      restartedL0 a m 0 y p =
        (L0 a.par (m.market 0 p) (m.density 0 p) (crra a) (crra a) y : EReal)) ∧
    (∀ t ∈ Icc (0 : ℝ) a.par.T, ∀ y > 0, ∀ p ∈ Ioo (0 : ℝ) 1,
      v t y p = restartedL1 a m t y p ∧
      (vhat a v f t y p : EReal) = restartedL0 a m t y p) ∧
    (∀ t ∈ Icc (0 : ℝ) a.par.T, ∀ p ∈ Ioo (0 : ℝ) 1, ∀ x : ℝ, b a.par t < x →
      let ystar := inverseMarginal (vhat a v f) t (b a.par t-x) p
      0 < ystar ∧
      (∃! y : ℝ, 0 < y ∧ dy (vhat a v f) t y p = b a.par t-x) ∧
      dy (vhat a v f) t ystar p = b a.par t-x ∧
      Stops a m t p (hit a m f t p ystar) ∧
      candidateCost a m t p ystar (hit a m f t p ystar) = ENNReal.ofReal (x-b a.par t) ∧
      OptimalControls a m f t p x ystar) := by sorry

end RetirePartialInfo.Duality.Supplement
