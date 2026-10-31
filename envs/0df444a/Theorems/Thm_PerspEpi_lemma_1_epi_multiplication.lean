-- Prove2me | Theorems.Thm_PerspEpi_lemma_1_epi_multiplication
-- name    : PerspEpi.lemma_1_epi_multiplication
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:28.439263+00:00
-- url     : https://prove2.me/theorems/7b2741c7-67da-4078-a629-d4e9835a2d3e
-- title:
--   Lemma 1: $(\lambda\star\varphi)(x)\to\varphi^\infty(x)$ on $\operatorname{dom}\varphi$ and $\lambda\star\varphi\xrightarrow{e}\varphi^\infty$ as $\lambda\downarrow0$
-- statement:
--   Let $E$ be a finite-dimensional Euclidean space and $\varphi \in \Gamma_0(E)$ a proper, closed, convex function $E \to \mathbb R\cup\{+\infty\}$. Write $(\lambda\star\varphi)(x) = \lambda\varphi(x/\lambda)$ for the epi-multiplication and $\varphi^\infty$ for the horizon function ($\operatorname{epi}\varphi^\infty = (\operatorname{epi}\varphi)^\infty$). Then, as $\lambda \downarrow 0$,
--
--   1. $(\lambda\star\varphi)(x) \to \varphi^\infty(x)$ for every $x \in \operatorname{dom}\varphi$;
--   2. $\lambda\star\varphi \xrightarrow{e} \varphi^\infty$ (epi-convergence along every sequence $\lambda_k \downarrow 0$).
--
--   The lemma shows that the perspective map $\omega^\pi(z,\lambda)$, which equals $\lambda\star\omega$ for $\lambda>0$ and $\omega^\infty$ at $\lambda = 0$, is the right extension at $\lambda = 0$; it is used for Proposition 4(b).
--
--   **Formalization Note** Limits are in `EReal` (the value $+\infty$ is allowed).
--
--   Differences from the source:
--   - encoding: R̄ = ℝ ∪ {+∞}; f ∈ Γ0(E) → f : E → EReal with ThreeOpSplitting.ConvexRates.IsProperClosedConvex f (never ⊥, somewhere finite, lsc, convex epigraph); reason: Lean convention; the same functions
--   - encoding: λ ↓ 0 (every sequence λ_k ↓ 0) → the filter 𝓝[>] 0, and sequences of positive reals tending to 0; reason: every such sequence has a monotone subsequence; the limits are the same
--   - encoding: φ^∞ defined by epi φ^∞ = (epi φ)^∞ → horizonFn φ y = inf {a | (y, a) ∈ (epi φ)^∞} in EReal, +∞ on the empty set; reason: for φ ∈ Γ0(E) the cone (epi φ)^∞ is a closed epigraph, so this is the function with that epigraph
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, Lemma 1, p.4

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_horizonFn
import Definitions.Def_PerspEpi_epiMul
import Definitions.Def_PerspEpi_EpiConvRight

open Filter Topology

namespace PerspEpi

/-- **Lemma 1 (Variational convergence of epi-multiplication).** Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, p.4:
"Let φ ∈ Γ0(E). Then as λ ↓ 0, (λ ⋆ φ)(x) → φ^∞(x) for all x ∈ dom φ, and λ ⋆ φ →e φ^∞."

**Formalization Note.** `E` is a finite-dimensional real inner product space. Functions take
values in `EReal`; `f ∈ Γ0(E)` is the published `ThreeOpSplitting.ConvexRates.IsProperClosedConvex`
(never `⊥`, somewhere finite, lower semicontinuous, convex epigraph). `P_λ f` is `PerspEpi.prox`
(the unique minimizer), `P_C` is `PerspEpi.projC` (the unique nearest point), `d_C` is
`Metric.infDist`, `dom f` is the published `AubinLipschitz.effDom f = {x | f x ≠ ⊤}`, and `e_λ f`,
`f*`, `∂f` and Painlevé–Kuratowski convergence are the published `MoreauChance.Consistency.moreauEnv`,
`conj`, `subdiff` (empty outside `dom f`) and `PKConv`. `λ ⋆ φ` is `PerspEpi.epiMul`, `φ^∞` is `PerspEpi.horizonFn` (epi φ^∞ = (epi φ)^∞).
"As λ ↓ 0" is the filter `𝓝[>] 0` for the pointwise limit, and `PerspEpi.EpiConvRight` (every
positive sequence tending to `0`) for epi-convergence. -/
theorem lemma_1_epi_multiplication {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : E → EReal) (hφ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex φ) :
    (∀ x ∈ AubinLipschitz.effDom φ, Tendsto (fun lam : ℝ => epiMul lam φ x) (𝓝[>] 0) (𝓝 (horizonFn φ x))) ∧
      EpiConvRight (fun lam : ℝ => epiMul lam φ) (horizonFn φ) := by sorry

end PerspEpi
