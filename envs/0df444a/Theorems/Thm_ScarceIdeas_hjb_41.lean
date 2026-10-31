-- Prove2me | Theorems.Thm_ScarceIdeas_hjb_41
-- name    : ScarceIdeas.hjb_41
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:08.30779+00:00
-- url     : https://prove2.me/theorems/115387d6-77b1-473c-a26f-7f574da3d730
-- title:
--   HJB (41)–(42): $V$ is the limit of $V^{\Delta t}$ and the unique bounded solution, and it decreases (corrected: welfare (16))
-- statement:
--   Throughout, $r>0$ is the discount rate, $v/r$ the social value of filling the niche, $f$ a continuous probability density with $f>0$ on its support $[\underline c,\overline c]\subset[0,\infty)$ and distribution function $F$, $\underline c<v/r<\overline c$, and the prior $h_0$ of the arrival rate satisfies Assumption 1. Let $V$ be the value function. Then:
--
--   1. $V$ is continuously differentiable on $[0,\infty)$, with derivative $V'$;
--   2. $0\le V(\phi)\le v/r-\underline c$ for all $\phi\ge0$;
--   3. for every $\phi\ge0$ the HJB equation holds, with the maximum attained:
--   $$0=\max_{p\in[\underline c,\overline c]}\Bigl\{m_1(\phi)\int_{\underline c}^{p}\Bigl(\frac vr-c\Bigr)f(c)\,dc-\bigl(r+m_1(\phi)F(p)\bigr)V(\phi)+V'(\phi)F(p)\Bigr\};$$
--   4. $V$ is decreasing on $[0,\infty)$;
--   5. $V$ is the only such solution: every $W$ differentiable on $[0,\infty)$ with values in $[0,v/r-\underline c]$ that satisfies the HJB equation at every $\phi\ge0$ coincides with $V$ on $[0,\infty)$;
--   6. $\lim_{\Delta t\to0}V^{\Delta t}(\phi)=V(\phi)$: for all small $\Delta t>0$ the Bellman recursion (17)–(18) has a fixed point in $S$, and every family $V^{\Delta t}$ of such fixed points converges to $V$ at every $\phi\ge0$.
--
--   This identifies the value function of the control problem with the solution of a scalar first-order equation in the state $\phi$.
--
--   Differences from the source:
--
--   - correction: welfare (16): the integrand multiplies e^{−λϕ(t)} by h_{ϕ(t)}(λ) → V is the supremum of the corrected functional ∫ e^{−rt} (∫ λ h0(λ) e^{−λΦ(t)} dλ / Z(ϕ)) ∫_{c̲}^{u(t)} (v/r − c) f(c) dc dt (definition welfare); reason: h_{ϕ(t)} already contains e^{−λϕ(t)}, so (16) counts survival twice: for h0(λ) = e^{−λ} and F(p) = 1/2 the printed λ-integrand at ϕ(t) = 1 integrates to (1/2)·2/9, the Bayesian claim density is (1/2)·1/4; the corrected form is the limit of the Bellman recursion (17) used by every later step
--   - reading: maximisation over reward paths p(·) with p(t) ∈ [c̲, c̄] → supremum over measurable (on (0, ∞)) policies with values in [cL, cH] for t ≥ 0; reason: the paper names no policy class; measurability makes every integral a genuine one
--   - encoding: all ϕ; dV/dϕ, dp/dϕ → ϕ ≥ 0, derivatives within [0, ∞); reason: the state ϕ = ∫F ≥ 0 lives in ℝ₊ (the space S, p.36); one-sided derivatives at the boundary state 0
--   - reading: V(ϕ) ∈ S is the unique solution to (41) and (42) → uniqueness among all W differentiable on [0, ∞) with values in [0, v/r − c̲] satisfying (41) at every ϕ ≥ 0; reason: (41) contains dV/dϕ, so a solution is differentiable (and so continuous, as S requires); no continuity of W' is imposed, the stronger reading
--   - generalization: V is a solution of (41) → V is continuously differentiable on [0, ∞); reason: the paper proves V continuously differentiable in Part 2 (p.38); a C¹ solution is in particular a solution
--   - encoding: max_p in (41), with p ∈ [c̲, c̄] as in (19) → IsGreatest of the bracket's image of [cL, cH] with value 0; reason: says the maximum exists and equals 0
--   - reading: Since V^Δt(ϕ) is decreasing in ϕ, so is V(ϕ) → V is antitone (weakly decreasing) on [0, ∞); reason: Part 1 obtains this as the pointwise limit of decreasing V^Δt, which preserves weak monotonicity; strict decrease is Theorem 3's claim and is stated in the goal
--   - reading: lim_{∆t→0} V^∆t(ϕ) = V(ϕ), with V^∆t the unique fixed point of T(∆t) in S → for all small ∆t > 0 a fixed point in S exists, and every family of such fixed points converges at every ϕ ≥ 0 to the supremum V of the corrected welfare; reason: the page takes V as this limit and as the maximum in (16); the clause states that the two agree, which is what justifies the correction of (16); the operator is used for small ∆t (it needs m_1(ϕ)∆t ≤ 1), and ∆t → 0 is from the right
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, Appendix, proof of Theorem 3, Part 1, (41)–(42), p.37; (19), p.22

import Mathlib
import Definitions.Def_ScarceIdeas_CostDensity
import Definitions.Def_ScarceIdeas_Assumption1
import Definitions.Def_ScarceIdeas_valueFn
import Definitions.Def_ScarceIdeas_hjbBracket
import Definitions.Def_ScarceIdeas_IsBellmanFixedPoint

namespace ScarceIdeas

open Filter Topology

/-- **The value function is the limit of the discrete-time values and the unique solution of the
HJB equation (41)–(42), and it is decreasing.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
Appendix, proof of Theorem 3, Part 1, (41)–(42), p.37 (also (19), p.22; the space `S`, p.36).

Under the standing assumptions (`r > 0`; `f` a continuous positive density on `[c̲, c̄]`;
`c̲ < v/r < c̄`; Assumption 1), the value function `V` (the supremum of the welfare over all
admissible policies) satisfies:
1. `V` is continuously differentiable on `[0, ∞)`, with derivative `V'`;
2. `0 ≤ V(ϕ) ≤ v/r − c̲` for every `ϕ ≥ 0`;
3. the HJB equation holds with the maximum attained: for every `ϕ ≥ 0`,
   $$0=\max_{p\in[\underline c,\overline c]}\Bigl\{m_1(\phi)\int_{\underline c}^{p}\Bigl(\frac vr-c\Bigr)f(c)dc
   -(r+m_1(\phi)F(p))V(\phi)+V'(\phi)F(p)\Bigr\};$$
4. `V` is decreasing on `[0, ∞)`;
5. `V` is the unique such solution: every `W` differentiable on `[0, ∞)` with values in
   `[0, v/r − c̲]` that satisfies (41) at every `ϕ ≥ 0` equals `V` on `[0, ∞)`;
6. `lim_{Δt→0} V^{Δt}(ϕ) = V(ϕ)`: for all small `Δt > 0` the Bellman recursion (17)–(18) has a fixed
   point in `S`, and every family `V^{Δt}` of such fixed points converges to `V` at every `ϕ ≥ 0`.

**Formalization Note** `IsGreatest (H '' [c̲, c̄]) 0` says the maximum in (41) exists and equals
`0`. Derivatives are within `[0, ∞)`. The competitors `W` in the uniqueness clause need only be
differentiable (no continuity of `W'`), the weakest reading of "solution". Clause 6 is what ties
the supremum `V` of the corrected welfare (16) to the recursion (17) the paper solves; `Δt → 0` is
from the right. -/
theorem hjb_41 (r v cL cH : ℝ) (f h0 : ℝ → ℝ) (hr : 0 < r) (hf : CostDensity cL cH f)
    (hvL : cL < v / r) (hvH : v / r < cH) (h0A : Assumption1 h0) :
    ∃ V' : ℝ → ℝ,
      (∀ ϕ : ℝ, 0 ≤ ϕ → HasDerivWithinAt (valueFn r v cL cH f h0) (V' ϕ) (Set.Ici 0) ϕ) ∧
      ContinuousOn V' (Set.Ici 0) ∧
      (∀ ϕ : ℝ, 0 ≤ ϕ → valueFn r v cL cH f h0 ϕ ∈ Set.Icc 0 (v / r - cL)) ∧
      (∀ ϕ : ℝ, 0 ≤ ϕ →
        IsGreatest
          ((fun p => hjbBracket r v cL f h0 ϕ (valueFn r v cL cH f h0 ϕ) (V' ϕ) p) ''
            Set.Icc cL cH) 0) ∧
      AntitoneOn (valueFn r v cL cH f h0) (Set.Ici 0) ∧
      (∀ W W' : ℝ → ℝ,
        (∀ ϕ : ℝ, 0 ≤ ϕ → HasDerivWithinAt W (W' ϕ) (Set.Ici 0) ϕ) →
        (∀ ϕ : ℝ, 0 ≤ ϕ → W ϕ ∈ Set.Icc 0 (v / r - cL)) →
        (∀ ϕ : ℝ, 0 ≤ ϕ →
          IsGreatest ((fun p => hjbBracket r v cL f h0 ϕ (W ϕ) (W' ϕ) p) '' Set.Icc cL cH) 0) →
        ∀ ϕ : ℝ, 0 ≤ ϕ → W ϕ = valueFn r v cL cH f h0 ϕ) ∧
      (∀ᶠ Δt in 𝓝[>] (0 : ℝ), ∃ W, IsBellmanFixedPoint r v cL cH f h0 Δt W) ∧
      ∀ Vd : ℝ → ℝ → ℝ,
        (∀ᶠ Δt in 𝓝[>] (0 : ℝ), IsBellmanFixedPoint r v cL cH f h0 Δt (Vd Δt)) →
        ∀ ϕ : ℝ, 0 ≤ ϕ →
          Tendsto (fun Δt => Vd Δt ϕ) (𝓝[>] (0 : ℝ)) (𝓝 (valueFn r v cL cH f h0 ϕ)) := by sorry

end ScarceIdeas
