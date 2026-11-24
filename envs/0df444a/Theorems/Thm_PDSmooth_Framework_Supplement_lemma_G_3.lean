-- Prove2me | Theorems.Thm_PDSmooth_Framework_Supplement_lemma_G_3
-- name    : PDSmooth.Framework.Supplement.lemma_G_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:54:16.086462+00:00
-- url     : https://prove2.me/theorems/782870d1-a2cc-4908-bd04-6088f1531bb7
-- title:
--   Lemma G.3, p. 42 — upper bounds ψ*_t ≤ A_tP* + L̄D(u*,u₀) (G.11) and, for bounded U, ψ*_t ≤ A_tΞ(v̄_t) + L̄Ω(u₀) (G.12)
-- statement:
--   Assume the standing assumptions of §5 and consider a run of Algorithm 2, with estimate functions $\psi_t$ (G.1) and $\psi_t^*=\min_{u\in\mathcal U}\psi_t(u)$.
--
--   1. If the oracle outputs are $(\delta_t,\bar L)$-FOAs of $h$ at $u_t$ and $u^*$ is an optimal solution of (5.1), then for every $t\ge0$
--   $$
--   \psi_t^*\ \le\ A_tP^*+\bar LD_{\omega_{\mathcal U}}(u^*,u_0). \tag{G.11}
--   $$
--   2. If $\mathcal U$ is bounded, $h$ has the max-structure (5.2), and $(\hat h(u_t),\hat\nabla h(u_t))=(\bar\Psi(u_t,v_t),\nabla_u\bar\Psi(u_t,v_t))$ for some $\{v_t\}_{t\ge0}\subseteq\mathcal V$ (which need not satisfy (5.21)), then $\Omega_{\omega_{\mathcal U}}(u_0)=\max_{u\in\mathcal U}D_{\omega_{\mathcal U}}(u,u_0)<+\infty$ and for every $t\ge0$
--   $$
--   \psi_t^*\ \le\ A_t\,\Xi(\bar v_t)+\bar L\,\Omega_{\omega_{\mathcal U}}(u_0), \tag{G.12}
--   $$
--   where $\bar v_t=A_t^{-1}\sum_{i=0}^t\alpha_iv_i$ (5.22) and $\Xi$ is the dual function (5.5).
--
--   These are the upper halves of the estimate-sequence argument: with Lemma G.1 they bound the primal gap and the duality gap.
--
--   **Formalization Note** The Lean statement proves the bounds at points: $\psi_t(u^*)\le A_tP(u^*)+\bar LD(u^*,u_0)$, and $\psi_t(x)\le A_t(\bar\Psi(x,\bar v_t)+\zeta(x)+\mu\omega_{\mathcal U}(x))+\bar L\Omega$ for every $x\in\mathcal U$. Since $\psi_t^*\le\psi_t(x)$ for every $x$, these give (G.11) and, taking the infimum over $x$ (with $A_t>0$), (G.12). Finiteness of $\Omega$ is part of the conclusion.
--
--   Differences from the source:
--   - generalization: ω_U is a DGF: continuous, 1-strongly convex on U and essentially smooth (continuously differentiable on int dom ω_U, gradient norm blowing up at the boundary) → ω_U continuous and 1-strongly convex on U and differentiable on an open convex set Wo standing for int dom ω_U; reason: the arguments use ∇ω_U only at points of U° = U ∩ Wo; essential smoothness serves only to place BPP solutions in U°, which the run (or the hypothesis on u⁺) states directly; every DGF of the page satisfies the Lean hypotheses
--   - encoding: ω_U : 𝕌 → ℝ ∪ {+∞}, U° = U ∩ int dom ω_U → ω : 𝕌 → ℝ whose values off U are unused, and U° = U ∩ Wo with Wo open and convex; reason: Lean convention; the interior of the domain of a convex function is open and convex, and only values on U enter
--   - generalization: ζ has an easily computable BPP on U with DGF ω_U (every subproblem (5.17) has a unique solution in U°) → no BPP hypothesis on ζ; the run supplies its own minimizers, each lying in U°; reason: the proofs use only the minimizers the run actually computes; under the page's BPP assumption those minimizers are unique and lie in U°, so every run of the page is a run of the Lean definition
--   - encoding: input L̄ ≥ L_h (presupposing L̄ > 0, since θ := μ/L̄ and the initial subproblem carries L̄D) → L̄ > 0 and L_h ≤ L̄ in the run; reason: a nondegeneracy condition the page presupposes; it excludes only the undefined case L̄ = 0
--   - encoding: u* an optimal solution of (5.1), P* = P(u*) → any u* ∈ U with P(u*) ≤ P(x) for all x ∈ U; reason: the same object
--   - generalization: ψ*_t ≤ A_tP* + L̄D(u*,u₀) (G.11) and ψ*_t ≤ A_tΞ(v̄_t) + L̄Ω(u₀) (G.12) → ψ_t(u*) ≤ A_tP(u*) + L̄D(u*,u₀), and ∀ x ∈ U, ψ_t(x) ≤ A_t(Ψ̄(x,v̄_t) + ζ(x) + μω(x)) + L̄Ω; reason: pointwise bounds, which are what the proof (G.13), (G.15) shows; since ψ*_t ≤ ψ_t(x) for all x they imply (G.11) and, after the infimum over x, (G.12)
--   - encoding: Ω_{ω_U}(u₀) := max_{u∈U} D_{ω_U}(u,u₀) < +∞ (5.26) → Ω = sSup of {D(u,u₀) : u ∈ U}, and BddAbove of that set is part of the conclusion; reason: the page's claim "< +∞" is proved, not assumed, so the real supremum is not a junk value
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 42, Lemma G.3, (G.11), (G.12), with (5.22) (p. 23), (5.5) (p. 20), (5.26) (p. 24)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Supplement_Problem
import Definitions.Def_PDSmooth_Framework_Supplement_FOA
import Definitions.Def_PDSmooth_Framework_Supplement_Alg2

namespace PDSmooth.Framework.Supplement

open PDSmooth.Framework

/-- Lemma G.3, p. 42, for a run of Algorithm 2.
(G.11): if the oracle outputs are `(δ_t, L̄)`-FOAs and `u*` minimizes `P` over `U`, then
`ψ_t(u*) ≤ A_t P* + L̄ D(u*, u₀)` for all `t` (hence `ψ*_t ≤ A_t P* + L̄ D(u*, u₀)`).
(G.12): if `U` is bounded, `h` has the max-structure, and `(ĥ_t, ĝ_t) = (Ψ̄(u_t,v_t), ∇_uΨ̄(u_t,v_t))`
for some `v_t ∈ V` (not required to satisfy (5.21)), then `D(·, u₀)` is bounded above on `U`
(`Ω(u₀) < +∞`) and `ψ_t(x) ≤ A_t (Ψ̄(x, v̄_t) + ζ(x) + μω(x)) + L̄Ω(u₀)` for all `t` and `x ∈ U`
(hence `ψ*_t ≤ A_t Ξ(v̄_t) + L̄Ω(u₀)`). -/
theorem lemma_G_3 {UU VV : Type*} [NormedAddCommGroup UU] [NormedSpace ℝ UU] [FiniteDimensional ℝ UU]
    [NormedAddCommGroup VV] [NormedSpace ℝ VV] [FiniteDimensional ℝ VV]
    {U U' Wo : Set UU} {h ζ ω : UU → ℝ} {Lh μ : ℝ} (hS : Sec5Setting U U' Wo h ζ ω Lh μ)
    (Lbar : ℝ) (α δ hhat : ℕ → ℝ) (ghat s : ℕ → UU →L[ℝ] ℝ) (u ubar z w : ℕ → UU)
    (hrun : IsAlg2Run U Wo ζ ω μ Lh Lbar α δ hhat ghat s u ubar z w) :
    ((∀ t, IsFOA h U (δ t) Lbar (u t) (hhat t) (ghat t)) →
      ∀ ustar ∈ U, (∀ x ∈ U, Pobj h ζ ω μ ustar ≤ Pobj h ζ ω μ x) →
      ∀ t : ℕ, psiEst ζ ω μ Lbar α hhat ghat u t ustar
        ≤ accW α t * Pobj h ζ ω μ ustar + Lbar * bregman ω ustar (u 0)) ∧
    (∀ (V V' : Set VV) (Ψ : UU → VV → ℝ) (Luu Luv ρv : ℝ) (v : ℕ → VV),
      MaxStructure U U' h V V' Ψ Luu Luv ρv → Bornology.IsBounded U → (∀ t, v t ∈ V) →
      (∀ t, hhat t = Ψ (u t) (v t) ∧ ghat t = fderiv ℝ (fun y => Ψ y (v t)) (u t)) →
      BddAbove ((fun x => bregman ω x (u 0)) '' U) ∧
      ∀ t : ℕ, ∀ x ∈ U, psiEst ζ ω μ Lbar α hhat ghat u t x
        ≤ accW α t * dualInner Ψ ζ ω μ (vbar α v t) x + Lbar * OmegaU ω U (u 0)) := by sorry

end PDSmooth.Framework.Supplement
