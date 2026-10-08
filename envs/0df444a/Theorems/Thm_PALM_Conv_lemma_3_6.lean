-- Prove2me | Theorems.Thm_PALM_Conv_lemma_3_6
-- name    : PALM.Conv.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:56.912435+00:00
-- url     : https://prove2.me/theorems/7bf32b92-6259-4879-bfb7-11b142345bce
-- title:
--   Lemma 3.6 (Uniformized KL property) — one (ε, η, φ) serves every point of a compact set on which σ is constant
-- statement:
--   Let $\Omega$ be a compact set and $\sigma$ a proper, lower semicontinuous function with values in $(-\infty,+\infty]$. Assume that $\sigma$ is constant on $\Omega$ and has the Kurdyka–Łojasiewicz property at each point of $\Omega$. Then there exist $\varepsilon>0$, $\eta>0$ and a desingularizing function $\varphi\in\Phi_\eta$ such that for every $\bar u\in\Omega$ and every $u$ in
--   $$\{u:\operatorname{dist}(u,\Omega)<\varepsilon\}\cap[\sigma(\bar u)<\sigma(u)<\sigma(\bar u)+\eta]$$
--   one has
--   $$\varphi'\big(\sigma(u)-\sigma(\bar u)\big)\operatorname{dist}\big(0,\partial\sigma(u)\big)\ge1.$$
--
--   Here $\Phi_\eta$ is the class of continuous concave $\varphi:[0,\eta)\to\mathbb R_+$ with $\varphi(0)=0$, $C^1$ on $(0,\eta)$ with $\varphi'>0$ there, and $\partial$ is the limiting subdifferential. The lemma replaces the pointwise KL property by one inequality valid uniformly near the whole compact set, which is what the finite length argument of Theorem 3.1 needs.
--
--   **Formalization Note** The paper's $\mathbb R^d$ is generalized to a finite-dimensional real inner product space, so that the lemma applies on the Euclidean product $\mathbb R^n\times\mathbb R^m$. Following the published KL definitions, $\eta$ is a positive real (the paper allows $\eta=+\infty$; the two are equivalent by restricting $\varphi$), and the inequality is read as $\varphi'(\sigma(u)-\sigma(\bar u))\|v\|\ge1$ for every $v\in\partial\sigma(u)$, which is the same as the $\operatorname{dist}$ form with $\operatorname{dist}(0,\emptyset)=+\infty$. If $\Omega$ is empty the statement holds trivially, as on the page.
-- source:
--   Bolte, Sabach, Teboulle, Proximal alternating linearized minimization for nonconvex and nonsmooth problems, Math. Program. 146 (2014), doi:10.1007/s10107-013-0701-9 (source: author version), p. 20, Lemma 3.6, (3.28)–(3.29)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ProxAltMin_Conv_Setting
import Definitions.Def_PALM_Conv_Setting
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL ProxAltMin.Conv PALM.Conv
open Filter Topology

namespace PALM.Conv

/-- Lemma 3.6 (Uniformized KL property), p. 20: let `Ω` be compact and `σ` proper and lsc,
constant on `Ω` and with the KL property at each point of `Ω`. Then there are `ε > 0`, `η > 0`
and `φ ∈ Φ_η` such that for every `ū ∈ Ω` and every `u` with `dist(u, Ω) < ε` and
`σ(ū) < σ(u) < σ(ū) + η` (3.28), `φ'(σ(u) - σ(ū)) dist(0, ∂σ(u)) ≥ 1` (3.29).
The paper's `ℝᵈ` is a finite-dimensional real inner product space here. -/
theorem lemma_3_6 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] (Ω : Set X) (hΩ : IsCompact Ω) (σ : X → EReal)
    (hσp : IsProperFn σ) (hσl : LowerSemicontinuous σ)
    (hconst : ∃ μ : EReal, ∀ u ∈ Ω, σ u = μ) (hKL : ∀ u ∈ Ω, HasKLProperty σ u) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ η : ℝ, 0 < η ∧ ∃ φ : ℝ → ℝ, IsDesingularizer η φ ∧
      ∀ ubar ∈ Ω, KLIneq σ ubar η {u | Metric.infDist u Ω < ε} φ := by sorry

end PALM.Conv
