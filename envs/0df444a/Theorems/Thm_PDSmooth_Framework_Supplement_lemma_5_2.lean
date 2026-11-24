-- Prove2me | Theorems.Thm_PDSmooth_Framework_Supplement_lemma_5_2
-- name    : PDSmooth.Framework.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:56:41.458874+00:00
-- url     : https://prove2.me/theorems/3b679b0f-9c09-4199-84e3-89116265d541
-- title:
--   Lemma 5.2, p. 26 — the inexact gradient mapping bounds the suboptimality: P(u⁺) − P* ≤ 3(‖Ḡ‖²_* + ‖G‖² + ‖e(ū)‖²_*)/(2μ)
-- statement:
--   Assume the standing assumptions of §5 with $\mu>0$. Given $u,\bar u\in\mathcal U^o$, a step $\lambda>0$ and an error $e(\bar u)\in\mathbb U^*$ on the gradient $\nabla h(\bar u)$, let
--
--   $$
--   u^+:=\operatorname*{arg\,min}_{u'\in\mathcal U}\ \langle\nabla h(\bar u)+e(\bar u),u'\rangle+\zeta(u')+\mu\omega_{\mathcal U}(u')+\lambda^{-1}D_{\omega_{\mathcal U}}(u',u), \tag{5.34}
--   $$
--
--   with $u^+\in\mathcal U^o$, and define
--
--   $$
--   G:=L_h(u^+-\bar u)\qquad\text{and}\qquad\bar G:=\lambda^{-1}\big(\nabla\omega_{\mathcal U}(u)-\nabla\omega_{\mathcal U}(u^+)\big). \tag{5.35}
--   $$
--
--   Then
--
--   $$
--   P(u^+)-P^*\ \le\ 3\big(\|\bar G\|_*^2+\|G\|^2+\|e(\bar u)\|_*^2\big)/(2\mu). \tag{5.36}
--   $$
--
--   The lemma bounds the optimality gap of one inexact Bregman proximal-gradient step by computable quantities; it yields the stopping test of Theorem 5.3.
--
--   **Formalization Note** $G$ is a primal vector (norm of $\mathbb U$), and $\bar G$ and $e(\bar u)$ are dual vectors (operator norm). The page prints $\nabla\omega_{\mathcal X}$ in (5.35); it is $\nabla\omega_{\mathcal U}$, the DGF of (5.34). The step size $\lambda$ of §5.4 is unrelated to the smoothing parameter $\lambda$ of §4 and is written `lamStep`. The page presents $u^+$ as the BPP solution, which lies in $\mathcal U^o$; the Lean takes any minimizer in $\mathcal U^o$.
--
--   Differences from the source:
--   - generalization: ω_U is a DGF: continuous, 1-strongly convex on U and essentially smooth (continuously differentiable on int dom ω_U, gradient norm blowing up at the boundary) → ω_U continuous and 1-strongly convex on U and differentiable on an open convex set Wo standing for int dom ω_U; reason: the arguments use ∇ω_U only at points of U° = U ∩ Wo; essential smoothness serves only to place BPP solutions in U°, which the run (or the hypothesis on u⁺) states directly; every DGF of the page satisfies the Lean hypotheses
--   - encoding: ω_U : 𝕌 → ℝ ∪ {+∞}, U° = U ∩ int dom ω_U → ω : 𝕌 → ℝ whose values off U are unused, and U° = U ∩ Wo with Wo open and convex; reason: Lean convention; the interior of the domain of a convex function is open and convex, and only values on U enter
--   - encoding: P(·) − P* with P* = min_{u∈U} P(u) → P(·) − P(x) for every x ∈ U; reason: equivalent to the bound on P(·) − P* for the minimum P*, and needs no separate minimizer
--   - encoding: ∇ω_𝒳 in (5.35) → ∇ω_U (fderiv ℝ ω); reason: a misprint: (5.34) uses ω_U, and 𝒳 is not in the setting of §5
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 26, Lemma 5.2, (5.34)–(5.36) (proof Appendix H, p. 43)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Supplement_Problem

namespace PDSmooth.Framework.Supplement

open PDSmooth.Framework

/-- Lemma 5.2, p. 26 (§5.4, `μ > 0`): for `u, ū ∈ U°`, a step `λ > 0`, a gradient error `e ∈ 𝕌*` and
`u⁺ ∈ U°` minimizing `⟨∇h(ū) + e, u'⟩ + ζ(u') + μω(u') + λ⁻¹D(u',u)` over `U` (5.34), with
`G = L_h(u⁺ − ū)` and `Ḡ = λ⁻¹(∇ω(u) − ∇ω(u⁺))` (5.35),
`P(u⁺) − P* ≤ 3(‖Ḡ‖²_* + ‖G‖² + ‖e‖²_*)/(2μ)` (5.36); `P*` is the minimum of `P` on `U`, and the bound
is stated against every `x ∈ U`. -/
theorem lemma_5_2 {UU : Type*} [NormedAddCommGroup UU] [NormedSpace ℝ UU] [FiniteDimensional ℝ UU]
    {U U' Wo : Set UU} {h ζ ω : UU → ℝ} {Lh μ : ℝ} (hS : Sec5Setting U U' Wo h ζ ω Lh μ)
    (hμ : 0 < μ) (u ubar uplus : UU) (hu : u ∈ U ∩ Wo) (hubar : ubar ∈ U ∩ Wo)
    (lamStep : ℝ) (hlam : 0 < lamStep) (e : UU →L[ℝ] ℝ)
    (huplus : uplus ∈ U ∩ Wo ∧ ∀ x ∈ U,
      (fderiv ℝ h ubar + e) uplus + ζ uplus + μ * ω uplus + lamStep⁻¹ * bregman ω uplus u
        ≤ (fderiv ℝ h ubar + e) x + ζ x + μ * ω x + lamStep⁻¹ * bregman ω x u) :
    ∀ x ∈ U, Pobj h ζ ω μ uplus - Pobj h ζ ω μ x
      ≤ 3 * (‖lamStep⁻¹ • (fderiv ℝ ω u - fderiv ℝ ω uplus)‖ ^ 2 + ‖Lh • (uplus - ubar)‖ ^ 2
          + ‖e‖ ^ 2) / (2 * μ) := by sorry

end PDSmooth.Framework.Supplement
