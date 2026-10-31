-- Prove2me | Theorems.Thm_PerspEpi_proposition_4_moreau_envelope_convergence
-- name    : PerspEpi.proposition_4_moreau_envelope_convergence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:26.393004+00:00
-- url     : https://prove2.me/theorems/af263601-f0f0-4253-8513-ae8be9424837
-- title:
--   Proposition 4: convergence of the Moreau envelope as $\lambda\downarrow0$, parts (a)–(e)
-- statement:
--   Let $E$ be a finite-dimensional Euclidean space and $f \in \Gamma_0(E)$; write $C = \operatorname{cl}(\operatorname{dom} f)$, $d_C$ for the distance to $C$, $N_C = \partial\delta_C$ for its normal cone and $e_\lambda f$ for the Moreau envelope. As $\lambda \downarrow 0$:
--
--   1. **(a)** $e_\lambda f \xrightarrow{e} f$ and $e_\lambda f \to f$ pointwise; in fact $e_\lambda f(x) \uparrow f(x)$ for all $x$, i.e. $\lambda \mapsto e_\lambda f(x)$ is nonincreasing on $(0,\infty)$ and tends to $f(x)$.
--   2. **(b)** $\lambda f \xrightarrow{e} \delta_C$.
--   3. **(c)** For every $\bar x \in E$,
--   $$
--   \lambda\, e_\lambda f(x) \to \tfrac12 d_C^2(\bar x) \qquad \text{as } x \to \bar x,\ \lambda\downarrow 0 \text{ (jointly)}.
--   $$
--   4. **(d)** $\lambda\partial f$ converges graphically to $N_C$: for every sequence $\lambda_k\downarrow 0$ the graphs $\{(x,\lambda_k v) \mid v \in \partial f(x)\}$ converge to $\operatorname{gph} N_C$ in the sense of Painlevé–Kuratowski.
--   5. **(e)** For $x \in \operatorname{dom}\partial f$ the least-norm subgradient $g_0 = \operatorname{argmin}_{g\in\partial f(x)}\|g\|$ is unique and
--   $$
--   \nabla e_\lambda f(x) = \tfrac1\lambda\big(x - P_\lambda f(x)\big) \to g_0 .
--   $$
--
--   These limits are the analytic basis for extending the envelope and the proximal map to $\lambda = 0$ (the functions $p_f$ and $P_f$).
--
--   **Formalization Note** Limits and $\lambda f$ (with $\lambda\cdot(+\infty) = +\infty$) are in `EReal`; graphs live in `E × E` with the product metric, which has the same convergent sequences as the Euclidean one.
--
--   Differences from the source:
--   - encoding: R̄ = ℝ ∪ {+∞}; f ∈ Γ0(E) → f : E → EReal with ThreeOpSplitting.ConvexRates.IsProperClosedConvex f (never ⊥, somewhere finite, lsc, convex epigraph); reason: Lean convention; the same functions
--   - encoding: λ ↓ 0 (every sequence λ_k ↓ 0) → the filter 𝓝[>] 0, and sequences of positive reals tending to 0; reason: every such sequence has a monotone subsequence; the limits are the same
--   - encoding: ∇e_λ f(x) → λ⁻¹ • (x − P_λ f(x)); reason: the gradient formula stated on p.14 just before the proposition
--   - encoding: λ∂f converges to N_cl(dom f) graphically [39, Def 5.32] → PKConv of the graphs {(x, λ_k v) | v ∈ ∂f(x)} ⊆ E × E to {(x, v) | v ∈ N_C(x)} for every λ_k ↓ 0; reason: graphical convergence is Painlevé–Kuratowski convergence of graphs; the product metric of E × E is equivalent to the Euclidean one
--   - encoding: e_λ f(x) ↑ f(x) → λ ↦ e_λ f(x) antitone on (0, ∞) together with the pointwise limit; reason: monotone convergence as λ decreases to 0
--   - encoding: e_λ f defined as a min → the infimum ⨅ in EReal (MoreauChance.Consistency.moreauEnv); reason: for f ∈ Γ0(E) and λ > 0 the minimum is attained, so the value is the same
--   - encoding: (c) λe_λ f(x) to ½d²(x̄) as x tends to x̄ and λ ↓ 0 → Tendsto along 𝓝 x̄ ×ˢ 𝓝[>] 0 for every x̄; reason: the product filter is the joint limit; the proof gives continuous convergence
--   - encoding: (e) the limit argmin_{g∈∂f(x)} ‖g‖ → ∃ g₀ with the set of least-norm subgradients equal to {g₀}, and the limit is g₀; reason: ∂f(x) is nonempty, closed and convex, so the argmin is a singleton and g₀ is the page's point
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, Proposition 4, p.14

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_ind
import Definitions.Def_MoreauChance_Consistency_Basic
import Definitions.Def_PerspEpi_prox
import Definitions.Def_PerspEpi_EpiConvRight

open Filter Topology

namespace PerspEpi

/-- **Proposition 4 (Convergence of the Moreau envelope).** Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, p.14:
"For f ∈ Γ0(E), the following hold as λ ↓ 0:
(a) e_λ f →e f and e_λ f →p f (in fact e_λ f(x) ↑ f(x) for all x ∈ E);
(b) λf →e δ_cl(dom f);
(c) λe_λ f(x) → ½d²_cl(dom f)(x̄) as x → x̄;
(d) λ∂f converges to N_cl(dom f) graphically in the sense of [39, Definition 5.32];
(e) for x ∈ dom ∂f we have ∇e_λ f(x) → argmin_{g∈∂f(x)} ‖g‖."

**Formalization Note.** `E` is a finite-dimensional real inner product space. Functions take
values in `EReal`; `f ∈ Γ0(E)` is the published `ThreeOpSplitting.ConvexRates.IsProperClosedConvex`
(never `⊥`, somewhere finite, lower semicontinuous, convex epigraph). `P_λ f` is `PerspEpi.prox`
(the unique minimizer), `P_C` is `PerspEpi.projC` (the unique nearest point), `d_C` is
`Metric.infDist`, `dom f` is the published `AubinLipschitz.effDom f = {x | f x ≠ ⊤}`, and `e_λ f`,
`f*`, `∂f` and Painlevé–Kuratowski convergence are the published `MoreauChance.Consistency.moreauEnv`,
`conj`, `subdiff` (empty outside `dom f`) and `PKConv`.
(a) "↑" is monotone convergence: `λ ↦ e_λ f(x)` is nonincreasing on `(0, ∞)` and tends to `f(x)`.
(b) `λf` is `x ↦ λ · f(x)` (`λ · (+∞) = +∞`), `δ_C` is `PerspEpi.ind C`.
(c) is a joint limit in `(x, λ)`: the filter `𝓝 x̄ ×ˢ 𝓝[>] 0`, for every `x̄ ∈ E`.
(d) Graphical convergence of `λ_k ∂f` to `N_C = ∂δ_C` ([39, Def 5.32]) is Painlevé–Kuratowski
convergence (`MoreauChance.Consistency.PKConv`) of the graphs `{(x, v) | v ∈ λ_k ∂f(x)} ⊆ E × E`, for every
sequence `λ_k` of positive reals tending to `0`.
(e) `∇e_λ f(x) = (1/λ)(x − P_λ f(x))` (p.14); the minimal-norm subgradient set is a singleton
`{g₀}` and the gradient tends to `g₀`. -/
theorem proposition_4_moreau_envelope_convergence {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) :
    -- (a)
    (EpiConvRight (fun lam : ℝ => MoreauChance.Consistency.moreauEnv f lam) f ∧
      (∀ x : E, Tendsto (fun lam : ℝ => MoreauChance.Consistency.moreauEnv f lam x) (𝓝[>] 0) (𝓝 (f x))) ∧
      (∀ x : E, AntitoneOn (fun lam : ℝ => MoreauChance.Consistency.moreauEnv f lam x) (Set.Ioi 0))) ∧
    -- (b)
    EpiConvRight (fun (lam : ℝ) (x : E) => (lam : EReal) * f x) (ind (closure (AubinLipschitz.effDom f))) ∧
    -- (c)
    (∀ xbar : E, Tendsto (fun q : E × ℝ => (q.2 : EReal) * MoreauChance.Consistency.moreauEnv f q.2 q.1)
      (𝓝 xbar ×ˢ 𝓝[>] 0)
      (𝓝 (((1 / 2) * Metric.infDist xbar (closure (AubinLipschitz.effDom f)) ^ 2 : ℝ) : EReal))) ∧
    -- (d)
    (∀ t : ℕ → ℝ, Tendsto t atTop (𝓝[>] 0) →
      MoreauChance.Consistency.PKConv (fun k => {p : E × E | ∃ v ∈ MoreauChance.Consistency.subdiff f p.1, p.2 = t k • v})
        {p : E × E | p.2 ∈ MoreauChance.Consistency.subdiff (ind (closure (AubinLipschitz.effDom f))) p.1}) ∧
    -- (e)
    (∀ x : E, (MoreauChance.Consistency.subdiff f x).Nonempty →
      ∃ g₀ : E, {g | g ∈ MoreauChance.Consistency.subdiff f x ∧ ∀ h ∈ MoreauChance.Consistency.subdiff f x, ‖g‖ ≤ ‖h‖} = {g₀} ∧
        Tendsto (fun lam : ℝ => lam⁻¹ • (x - prox f lam x)) (𝓝[>] 0) (𝓝 g₀)) := by sorry

end PerspEpi
