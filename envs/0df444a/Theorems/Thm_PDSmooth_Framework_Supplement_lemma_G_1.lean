-- Prove2me | Theorems.Thm_PDSmooth_Framework_Supplement_lemma_G_1
-- name    : PDSmooth.Framework.Supplement.lemma_G_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:53:08.916141+00:00
-- url     : https://prove2.me/theorems/2c892551-8550-4716-95b1-de5bb53967c9
-- title:
--   Lemma G.1, p. 40 — under (G.3), ψ*_t ≥ A_t P(z_t) − E_t for every run of Algorithm 2
-- statement:
--   Assume the standing assumptions of §5 and consider a run of Algorithm 2 whose oracle outputs $(\hat h(u_t),\hat\nabla h(u_t))$ are $(\delta_t,\bar L)$-FOAs of $h$ at $u_t$ for every $t\ge0$. Let $\psi_t$ be the estimate functions (G.1) and $\psi_t^*:=\min_{u\in\mathcal U}\psi_t(u)$ (G.2). If $\alpha_0=1$ and
--
--   $$
--   (A_t\mu+\bar L)A_{t+1}\ \ge\ \bar L\alpha_{t+1}^2\qquad\forall t\ge0, \tag{G.3}
--   $$
--
--   then for all $t\ge0$
--
--   $$
--   \psi_t^*\ \ge\ A_tP(z_t)-E_t,\qquad E_t:=\sum_{i=0}^tA_i\delta_i. \tag{G.4}
--   $$
--
--   This is the lower half of the estimate-sequence argument; combined with the upper bounds of Lemma G.3 it gives the rates of Theorems 5.1 and 5.2.
--
--   **Formalization Note** The bound on the minimum is stated against every point: $A_tP(z_t)-E_t\le\psi_t(x)$ for all $x\in\mathcal U$. The weights are any positive weights with $\alpha_0=1$ satisfying (G.3), for any $\mu\ge0$.
--
--   Differences from the source:
--   - generalization: ω_U is a DGF: continuous, 1-strongly convex on U and essentially smooth (continuously differentiable on int dom ω_U, gradient norm blowing up at the boundary) → ω_U continuous and 1-strongly convex on U and differentiable on an open convex set Wo standing for int dom ω_U; reason: the arguments use ∇ω_U only at points of U° = U ∩ Wo; essential smoothness serves only to place BPP solutions in U°, which the run (or the hypothesis on u⁺) states directly; every DGF of the page satisfies the Lean hypotheses
--   - encoding: ω_U : 𝕌 → ℝ ∪ {+∞}, U° = U ∩ int dom ω_U → ω : 𝕌 → ℝ whose values off U are unused, and U° = U ∩ Wo with Wo open and convex; reason: Lean convention; the interior of the domain of a convex function is open and convex, and only values on U enter
--   - generalization: ζ has an easily computable BPP on U with DGF ω_U (every subproblem (5.17) has a unique solution in U°) → no BPP hypothesis on ζ; the run supplies its own minimizers, each lying in U°; reason: the proofs use only the minimizers the run actually computes; under the page's BPP assumption those minimizers are unique and lie in U°, so every run of the page is a run of the Lean definition
--   - encoding: input L̄ ≥ L_h (presupposing L̄ > 0, since θ := μ/L̄ and the initial subproblem carries L̄D) → L̄ > 0 and L_h ≤ L̄ in the run; reason: a nondegeneracy condition the page presupposes; it excludes only the undefined case L̄ = 0
--   - encoding: ψ*_t ≥ A_tP(z_t) − E_t with ψ*_t = min_{u∈U} ψ_t(u) → ∀ x ∈ U, A_tP(z_t) − E_t ≤ ψ_t(x); reason: equivalent for a minimum over U, and free of a junk value of a real infimum
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 40, Lemma G.1, (G.1)–(G.4) (p. 39)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Supplement_Problem
import Definitions.Def_PDSmooth_Framework_Supplement_FOA
import Definitions.Def_PDSmooth_Framework_Supplement_Alg2

namespace PDSmooth.Framework.Supplement

/-- Lemma G.1, p. 40: for a run of Algorithm 2 whose oracle outputs `(ĥ_t, ĝ_t)` are
`(δ_t, L̄)`-FOAs of `h` at `u_t`, if `α₀ = 1` and `(A_tμ + L̄)A_{t+1} ≥ L̄α²_{t+1}` for all `t` (G.3),
then `ψ*_t ≥ A_t P(z_t) − E_t` for all `t` (G.4), where `ψ*_t = min_{x ∈ U} ψ_t(x)`; the bound is stated
against every `x ∈ U`. -/
theorem lemma_G_1 {UU : Type*} [NormedAddCommGroup UU] [NormedSpace ℝ UU] [FiniteDimensional ℝ UU]
    {U U' Wo : Set UU} {h ζ ω : UU → ℝ} {Lh μ : ℝ} (hS : Sec5Setting U U' Wo h ζ ω Lh μ)
    (Lbar : ℝ) (α δ hhat : ℕ → ℝ) (ghat s : ℕ → UU →L[ℝ] ℝ) (u ubar z w : ℕ → UU)
    (hrun : IsAlg2Run U Wo ζ ω μ Lh Lbar α δ hhat ghat s u ubar z w)
    (hfoa : ∀ t, IsFOA h U (δ t) Lbar (u t) (hhat t) (ghat t))
    (hα0 : α 0 = 1)
    (hG3 : ∀ t, Lbar * α (t + 1) ^ 2 ≤ (accW α t * μ + Lbar) * accW α (t + 1)) :
    ∀ t : ℕ, ∀ x ∈ U,
      accW α t * Pobj h ζ ω μ (z t) - errE α δ t ≤ psiEst ζ ω μ Lbar α hhat ghat u t x := by sorry

end PDSmooth.Framework.Supplement
