-- Prove2me | Theorems.Thm_PDSmooth_Framework_Supplement_lemma_5_1
-- name    : PDSmooth.Framework.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:52:36.589653+00:00
-- url     : https://prove2.me/theorems/4d84cc81-977a-447c-a558-4f635ee39c35
-- title:
--   Lemma 5.1, p. 21 — an approximate inner maximizer gives a (δ, 2L_h)-FOA of the max-structured h
-- statement:
--   Assume the standing assumptions of §5 and that $h$ has the max-structure (5.2)–(5.4) with $\rho>0$ and $L_h=L_{uu}+L_{uv}^2/\rho$. Let $u\in\mathcal U$, $\delta>0$, and let $\hat v\in\mathcal V$ satisfy $h(u)-\bar\Psi(u,\hat v)\le\delta/2$. Then for every $u'\in\mathcal U$,
--
--   $$
--   \begin{aligned}
--   h(u')&\ \ge\ \bar\Psi(u,\hat v)+\langle\nabla_u\bar\Psi(u,\hat v),u'-u\rangle, &&(5.8)\\
--   h(u')&\ \le\ \bar\Psi(u,\hat v)+\langle\nabla_u\bar\Psi(u,\hat v),u'-u\rangle+(\bar L/2)\|u'-u\|^2+\delta, &&(5.9)
--   \end{aligned}
--   $$
--
--   where $\bar L=2L_h$. In words, $(\bar\Psi(u,\hat v),\nabla_u\bar\Psi(u,\hat v))$ is a $(\delta,2L_h)$-FOA of $h$ at $u$.
--
--   The lemma is what makes an approximate solution of the inner maximization a valid inexact oracle for Algorithm 2, and it is the source of the duality-gap bounds of Theorems 5.1 and 5.2.
--
--   **Formalization Note** The gradient $\nabla h(u)=\nabla_u\bar\Psi(u,v^*(u))$ used in the paper's proof is not a hypothesis. The standing $L_h$-smoothness of $h$ and the formula $L_h=L_{uu}+L_{uv}^2/\rho$ are both assumed, as on the page; the max-structure hypotheses hold only on $\mathcal U$, so they do not give differentiability of $h$ on the open set $\mathcal U'$.
--
--   Differences from the source:
--   - generalization: ω_U is a DGF: continuous, 1-strongly convex on U and essentially smooth (continuously differentiable on int dom ω_U, gradient norm blowing up at the boundary) → ω_U continuous and 1-strongly convex on U and differentiable on an open convex set Wo standing for int dom ω_U; reason: the arguments use ∇ω_U only at points of U° = U ∩ Wo; essential smoothness serves only to place BPP solutions in U°, which the run (or the hypothesis on u⁺) states directly; every DGF of the page satisfies the Lean hypotheses
--   - encoding: ω_U : 𝕌 → ℝ ∪ {+∞}, U° = U ∩ int dom ω_U → ω : 𝕌 → ℝ whose values off U are unused, and U° = U ∩ Wo with Wo open and convex; reason: Lean convention; the interior of the domain of a convex function is open and convex, and only values on U enter
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 21, Lemma 5.1 (setting pp. 19–20, (5.2)–(5.4); proof Appendix F, p. 39)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Supplement_Problem
import Definitions.Def_PDSmooth_Framework_Supplement_FOA

namespace PDSmooth.Framework.Supplement

/-- Lemma 5.1, p. 21: under the standing assumptions of §5 and the max-structure (5.2)–(5.4) with
`L_h = L_uu + L_uv²/ρ`, for any `u ∈ U`, `δ > 0` and `v̂ ∈ V` with `h(u) − Ψ̄(u,v̂) ≤ δ/2`, the pair
`(Ψ̄(u,v̂), ∇_uΨ̄(u,v̂))` is a `(δ, 2L_h)`-FOA of `h` at `u`: (5.8) and (5.9) hold for all `u' ∈ U`. -/
theorem lemma_5_1 {UU VV : Type*} [NormedAddCommGroup UU] [NormedSpace ℝ UU] [FiniteDimensional ℝ UU]
    [NormedAddCommGroup VV] [NormedSpace ℝ VV] [FiniteDimensional ℝ VV]
    {U U' Wo : Set UU} {h ζ ω : UU → ℝ} {Lh μ : ℝ} (hS : Sec5Setting U U' Wo h ζ ω Lh μ)
    {V V' : Set VV} {Ψ : UU → VV → ℝ} {Luu Luv ρv : ℝ}
    (hM : MaxStructure U U' h V V' Ψ Luu Luv ρv) (hLh : Lh = Luu + Luv ^ 2 / ρv)
    (u : UU) (hu : u ∈ U) (δ : ℝ) (hδ : 0 < δ) (vhat : VV) (hvhat : vhat ∈ V)
    (happrox : h u - Ψ u vhat ≤ δ / 2) :
    IsFOA h U δ (2 * Lh) u (Ψ u vhat) (fderiv ℝ (fun y => Ψ y vhat) u) := by sorry

end PDSmooth.Framework.Supplement
