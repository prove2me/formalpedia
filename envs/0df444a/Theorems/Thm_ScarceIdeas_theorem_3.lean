-- Prove2me | Theorems.Thm_ScarceIdeas_theorem_3
-- name    : ScarceIdeas.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:12.315332+00:00
-- url     : https://prove2.me/theorems/33196af3-2c77-49fb-a165-66b394b7871f
-- title:
--   Theorem 3: the optimal reward solves (22), increases to $v/r$ at rate $\frac{2}{\phi r}\int_{\underline c}^{v/r}F$, and welfare decreases (corrected: welfare (16))
-- statement:
--   Throughout, $r>0$ is the discount rate, $v/r$ the social value of filling the niche, $f$ a continuous probability density with $f>0$ on its support $[\underline c,\overline c]\subset[0,\infty)$ and distribution function $F$, $\underline c<v/r<\overline c$, and the prior $h_0$ of the arrival rate satisfies Assumption 1. Then there is a feedback reward rule $p:\phi\mapsto p(\phi)\in[\underline c,\overline c]$ such that:
--
--   1. $p$ is an optimal reward policy: from every state $\phi_0\ge0$ its closed-loop paths exist, and each attains the value $V(\phi_0)$, the supremum of the expected welfare over all admissible policies;
--   2. (22) holds, $V(\phi)=\frac{m_1(\phi)}{r}\int_{\underline c}^{p(\phi)}F(c)\,dc$ for every $\phi\ge0$, and $p(\phi)$ is the unique solution of (22) in $[\underline c,\overline c]$;
--   3. $p$ is continuously differentiable and strictly increasing on $[0,\infty)$;
--   4. the value $V$ is strictly decreasing on $[0,\infty)$;
--   5. $p(\phi)\to v/r$, at the rate
--   $$p(\phi)=\frac vr-\frac{2}{\phi r}\int_{\underline c}^{v/r}F(c)\,dc+o\Bigl(\frac1\phi\Bigr)\qquad(\phi\to\infty).$$
--
--   When the arrival rate of ideas is unknown, the longer the niche stays open the more the planner should be willing to pay, while expected social welfare falls.
--
--   Differences from the source:
--
--   - correction: welfare (16): the integrand multiplies e^{−λϕ(t)} by h_{ϕ(t)}(λ) → V is the supremum of the corrected functional ∫ e^{−rt} (∫ λ h0(λ) e^{−λΦ(t)} dλ / Z(ϕ)) ∫_{c̲}^{u(t)} (v/r − c) f(c) dc dt (definition welfare); reason: h_{ϕ(t)} already contains e^{−λϕ(t)}, so (16) counts survival twice: for h0(λ) = e^{−λ} and F(p) = 1/2 the printed λ-integrand at ϕ(t) = 1 integrates to (1/2)·2/9, the Bayesian claim density is (1/2)·1/4; the corrected form is the limit of the Bellman recursion (17) used by every later step
--   - reading: maximisation over reward paths p(·) with p(t) ∈ [c̲, c̄] → supremum over measurable (on (0, ∞)) policies with values in [cL, cH] for t ≥ 0; reason: the paper names no policy class; measurability makes every integral a genuine one
--   - encoding: all ϕ; dV/dϕ, dp/dϕ → ϕ ≥ 0, derivatives within [0, ∞); reason: the state ϕ = ∫F ≥ 0 lives in ℝ₊ (the space S, p.36); one-sided derivatives at the boundary state 0
--   - reading: the optimal reward policy p(ϕ) → a feedback rule whose closed-loop paths, from every state, exist and attain V; reason: the paper treats the optimal policy as a function of ϕ (p.18) without fixing a solution concept
--   - reading: p(ϕ) is the unique solution to (22) → for each ϕ ≥ 0, p(ϕ) is the only q ∈ [c̲, c̄] with V(ϕ) = (m_1(ϕ)/r) ∫_{c̲}^{q} F; reason: uniqueness of the feedback function is false (changing p at one state changes no welfare); the page's uniqueness is that of the root of (22)
--   - reading: p(ϕ) increases, V(ϕ) decreases → StrictMonoOn p and StrictAntiOn V on [0, ∞); reason: the proof's Part 3 shows p strictly increasing, and V' < 0 is used in the proof of Theorem 6 (p.47); strict is the stronger reading
--   - generalization: Theorem 3's clauses → also p continuously differentiable on [0, ∞); reason: proved in Part 2 (p.38, "p(ϕ) is continuously differentiable"); an extra conclusion
--   - encoding: p(ϕ) = v/r − (2/(ϕr)) ∫_{c̲}^{v/r} F + o(1/ϕ) → ϕ (v/r − p(ϕ)) → (2/r) ∫_{c̲}^{v/r} F as ϕ → ∞, plus p → v/r; reason: equivalent by the definition of o(·)
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, Theorem 3, p.23, with (22), p.22; proof pp.36–40, (41)–(55)

import Mathlib
import Definitions.Def_ScarceIdeas_CostDensity
import Definitions.Def_ScarceIdeas_Assumption1
import Definitions.Def_ScarceIdeas_IsOptimalPolicy
import Definitions.Def_ScarceIdeas_moment

namespace ScarceIdeas

open Filter Topology

/-- **Theorem 3: the optimal reward solves (22), increases to `v/r` at rate `2/(ϕr)∫F`, and social
welfare decreases.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
Theorem 3, p.23, with (22), p.22; proof pp.36–40, (41)–(55).

Under the standing assumptions (`r > 0`; `f` a continuous positive probability density with support
`[c̲, c̄] ⊂ [0, ∞)`; `c̲ < v/r < c̄`; the prior `h₀` satisfies Assumption 1), there is a feedback
reward rule `p : ϕ ↦ p(ϕ) ∈ [c̲, c̄]` such that
1. `p` is an optimal reward policy: from every state its closed-loop paths exist and attain the
   value `V(ϕ)`, the supremum of welfare over all admissible policies;
2. (22) holds, `V(ϕ) = (m₁(ϕ)/r) ∫_{c̲}^{p(ϕ)} F(c) dc`, and `p(ϕ)` is its unique solution in
   `[c̲, c̄]`;
3. `p` is continuously differentiable and strictly increasing on `[0, ∞)`;
4. `V` is strictly decreasing on `[0, ∞)`;
5. `p(ϕ) → v/r` and
   $$p(\phi)=\frac vr-\frac{2}{\phi r}\int_{\underline c}^{v/r}F(c)\,dc+o\Bigl(\frac1\phi\Bigr),$$
   i.e. `ϕ (v/r − p(ϕ)) → (2/r) ∫_{c̲}^{v/r} F(c) dc` as `ϕ → ∞`.

**Formalization Note** States are `ϕ ≥ 0`. "Increases"/"decreases" are strict. `o(1/ϕ)` is
stated as a limit of `ϕ (v/r − p(ϕ))`. "Unique solution to (22)" is uniqueness of the reward at
each state; the feedback function itself is only pinned down by (22), since changing it at one
state changes no closed-loop welfare. -/
theorem theorem_3 (r v cL cH : ℝ) (f h0 : ℝ → ℝ) (hr : 0 < r) (hf : CostDensity cL cH f)
    (hvL : cL < v / r) (hvH : v / r < cH) (h0A : Assumption1 h0) :
    ∃ p : ℝ → ℝ,
      (∀ ϕ : ℝ, 0 ≤ ϕ → p ϕ ∈ Set.Icc cL cH) ∧
      IsOptimalPolicy r v cL cH f h0 p ∧
      (∀ ϕ : ℝ, 0 ≤ ϕ →
        valueFn r v cL cH f h0 ϕ = moment h0 1 ϕ / r * ∫ c in cL..p ϕ, costCDF cL f c) ∧
      (∀ ϕ : ℝ, 0 ≤ ϕ → ∀ q ∈ Set.Icc cL cH,
        valueFn r v cL cH f h0 ϕ = moment h0 1 ϕ / r * ∫ c in cL..q, costCDF cL f c →
          q = p ϕ) ∧
      ContDiffOn ℝ 1 p (Set.Ici 0) ∧
      StrictMonoOn p (Set.Ici 0) ∧
      StrictAntiOn (valueFn r v cL cH f h0) (Set.Ici 0) ∧
      Tendsto p atTop (𝓝 (v / r)) ∧
      Tendsto (fun ϕ : ℝ => ϕ * (v / r - p ϕ)) atTop
        (𝓝 (2 / r * ∫ c in cL..v / r, costCDF cL f c)) := by sorry

end ScarceIdeas
