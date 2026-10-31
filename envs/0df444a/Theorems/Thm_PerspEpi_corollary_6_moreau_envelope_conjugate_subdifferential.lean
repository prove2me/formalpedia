-- Prove2me | Theorems.Thm_PerspEpi_corollary_6_moreau_envelope_conjugate_subdifferential
-- name    : PerspEpi.corollary_6_moreau_envelope_conjugate_subdifferential
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:13.784992+00:00
-- url     : https://prove2.me/theorems/49df11a7-281f-458d-a97d-eefcdc3f91bf
-- title:
--   Corollary 6 (corrected: sign of the $\lambda=0$ subdifferential): $p_f\in\Gamma_0(E\times\mathbb R)$, its conjugate and subdifferential
-- statement:
--   Let $E$ be a finite-dimensional Euclidean space, $f\in\Gamma_0(E)$, and let $p_f(x,\lambda)$ be the extended Moreau envelope ($e_\lambda f(x)$ for $\lambda>0$, $f(x)$ for $\lambda = 0$, $+\infty$ for $\lambda<0$) on the Euclidean space $E\times\mathbb R$. Then $p_f\in\Gamma_0(E\times\mathbb R)$ and:
--
--   1. **(a)** For all $(y,\mu)$,
--   $$
--   p_f^*(y,\mu) = f^*(y) + \delta_{\operatorname{epi}\frac12\|\cdot\|^2}(y,-\mu),
--   $$
--   and $p_f^* \in \Gamma_0(E\times\mathbb R)$.
--   2. **(b)** For all $(x,\lambda) \in \operatorname{dom} p_f$,
--   $$
--   \partial p_f(x,\lambda) = \begin{cases} \Big\{\Big(\tfrac1\lambda[x - P_\lambda f(x)],\ -\tfrac12\big\|\tfrac1\lambda[x-P_\lambda f(x)]\big\|^2\Big)\Big\} & \lambda > 0,\\[4pt] \big\{(v,-\beta) \ \big|\ v\in\partial f(x),\ \tfrac12\|v\|^2 \le \beta\big\} & \lambda = 0. \end{cases}
--   $$
--
--   The corollary is the specialization of the paper's general infimal-convolution calculus (Corollary 1) to $\omega = \frac12\|\cdot\|^2$; it shows that the envelope is jointly convex in $(x,\lambda)$.
--
--   **Formalization Note** $E\times\mathbb R$ is `WithLp 2 (E × ℝ)` with inner product $\langle (v,\beta),(x,\lambda)\rangle = \langle v,x\rangle + \beta\lambda$.
--
--   Differences from the source:
--   - encoding: R̄ = ℝ ∪ {+∞}; f ∈ Γ0(E) → f : E → EReal with ThreeOpSplitting.ConvexRates.IsProperClosedConvex f (never ⊥, somewhere finite, lsc, convex epigraph); reason: Lean convention; the same functions
--   - correction: ∂p_f(x,0) = {(v,β) | −v ∈ ∂f(x), ½‖v‖² ≤ β} → ∂p_f(x,0) = {(v,−β) | v ∈ ∂f(x), ½‖v‖² ≤ β}; reason: the printed set is false: for E = ℝ, f(u) = u, (x,λ) = (0,0), it contains (−1, ½) but p_f(−1,0) = −1 < p_f(0,0) + ⟨(−1,½),(−1,0)⟩ = 1; the corrected set is Corollary 1(b) with ω = ½‖·‖², as the proof says
--   - encoding: E × ℝ with the Euclidean inner product; δ_{epi ½‖·‖²}(y,−µ) → WithLp 2 (E × ℝ); ind {(y,s) | ½‖y‖² ≤ s} at (y, −µ); reason: Lean convention; the same space and the same indicator
--   - encoding: e_λ f defined as a min → the infimum ⨅ in EReal (MoreauChance.Consistency.moreauEnv); reason: for f ∈ Γ0(E) and λ > 0 the minimum is attained, so the value is the same
--   - encoding: (b) for λ > 0, ∂p_f(x,λ) printed as one point → the singleton containing that point; reason: ∂p_f(x,λ) is a set and the printed point is its only element
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, Corollary 6, p.15

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_ind
import Definitions.Def_MoreauChance_Consistency_Basic
import Definitions.Def_PerspEpi_prox
import Definitions.Def_PerspEpi_extEnv

open Filter Topology

namespace PerspEpi

/-- **Corollary 6 (Conjugate and subdifferential of the Moreau envelope)**, with the `λ = 0` case of
(b) corrected. Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, p.15: "Let f ∈ Γ0(E). Then p_f ∈ Γ0(E × ℝ) and
(a) p*_f(y,µ) = f*(y) + δ_{epi ½‖·‖²}(y,−µ) and p*_f ∈ Γ0(E × ℝ);
(b) for all (x,λ) ∈ dom p_f, ∂p_f(x,λ) = ( (1/λ)[x − P_λ f(x)], −½‖(1/λ)[x − P_λ f(x)]‖² ) if λ > 0;
{(v,β) | −v ∈ ∂f(x), ½‖v‖² ≤ β} if λ = 0."

**Correction.** At `λ = 0` the page's set has a sign slip; the statement here is
`∂p_f(x, 0) = {(v, −β) | v ∈ ∂f(x), ½‖v‖² ≤ β}`, the specialization of the paper's Corollary 1(b)
with `ω = ½‖·‖²` that the proof invokes. Counterexample to the printed set: `E = ℝ`, `f(u) = u`,
`(x, λ) = (0, 0)`; the printed set contains `(−1, ½)`, but `p_f(−1, 0) = −1 < p_f(0,0) + ⟨(−1, ½), (−1, 0)⟩ = 1`.

**Formalization Note.** `E` is a finite-dimensional real inner product space. Functions take
values in `EReal`; `f ∈ Γ0(E)` is the published `ThreeOpSplitting.ConvexRates.IsProperClosedConvex`
(never `⊥`, somewhere finite, lower semicontinuous, convex epigraph). `P_λ f` is `PerspEpi.prox`
(the unique minimizer), `P_C` is `PerspEpi.projC` (the unique nearest point), `d_C` is
`Metric.infDist`, `dom f` is the published `AubinLipschitz.effDom f = {x | f x ≠ ⊤}`, and `e_λ f`,
`f*`, `∂f` and Painlevé–Kuratowski convergence are the published `MoreauChance.Consistency.moreauEnv`,
`conj`, `subdiff` (empty outside `dom f`) and `PKConv`. `E × ℝ` is the Euclidean space `WithLp 2 (E × ℝ)`, with inner product
`⟨(v, β), (x, λ)⟩ = ⟨v, x⟩ + βλ`; `p_f` is `PerspEpi.extEnv`. `δ_{epi ½‖·‖²}(y, −µ)` is the
indicator of `{(y, s) | ½‖y‖² ≤ s}` at `(y, −µ)`. -/
theorem corollary_6_moreau_envelope_conjugate_subdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) :
    ThreeOpSplitting.ConvexRates.IsProperClosedConvex (extEnv f) ∧
    -- (a)
    (∀ q : WithLp 2 (E × ℝ), MoreauChance.Consistency.conj (extEnv f) q =
      MoreauChance.Consistency.conj f q.fst + ind {p : E × ℝ | (1 / 2 : ℝ) * ‖p.1‖ ^ 2 ≤ p.2} (q.fst, -q.snd)) ∧
    ThreeOpSplitting.ConvexRates.IsProperClosedConvex (MoreauChance.Consistency.conj (extEnv f)) ∧
    -- (b)
    (∀ (x : E) (lam : ℝ), extEnv f (WithLp.toLp 2 (x, lam)) ≠ ⊤ →
      (0 < lam → MoreauChance.Consistency.subdiff (extEnv f) (WithLp.toLp 2 (x, lam)) =
        {WithLp.toLp 2 (lam⁻¹ • (x - prox f lam x), -(1 / 2) * ‖lam⁻¹ • (x - prox f lam x)‖ ^ 2)}) ∧
      (lam = 0 → MoreauChance.Consistency.subdiff (extEnv f) (WithLp.toLp 2 (x, lam)) =
        {q | ∃ v ∈ MoreauChance.Consistency.subdiff f x, ∃ β : ℝ, (1 / 2) * ‖v‖ ^ 2 ≤ β ∧ q = WithLp.toLp 2 (v, -β)})) := by sorry

end PerspEpi
