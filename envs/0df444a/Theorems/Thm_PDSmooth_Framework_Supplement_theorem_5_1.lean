-- Prove2me | Theorems.Thm_PDSmooth_Framework_Supplement_theorem_5_1
-- name    : PDSmooth.Framework.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:55:19.380321+00:00
-- url     : https://prove2.me/theorems/5dfa1757-42a5-400c-b6da-ef278344e728
-- title:
--   Theorem 5.1, p. 24 — for μ = 0, Algorithm 2 with α_t = (2t + 3)/4 has primal gap (5.24) and, for bounded U, duality gap (5.25) of order 1/(t + 2)²
-- statement:
--   Assume the standing assumptions of §5 with $\mu=0$, and consider a run of Algorithm 2 with weights
--
--   $$
--   \alpha_0=1\quad\text{and}\quad\alpha_t=(2t+3)/4,\quad\forall t\ge1. \tag{5.23}
--   $$
--
--   1. If the oracle outputs $(\hat h(u_t),\hat\nabla h(u_t))$ are $(\delta_t,\bar L)$-FOAs of $h$ at $u_t$ for all $t$, then for every optimal solution $u^*$ of (5.1)
--   $$
--   P(z_t)-P^*\ \le\ \frac{4\bar LD_{\omega_{\mathcal U}}(u^*,u_0)}{(t+2)^2}+\frac{\sum_{i=0}^t(i+2)^2\delta_i}{(t+2)^2},\qquad\forall t\ge0. \tag{5.24}
--   $$
--   2. If in addition to the standing assumptions $\mathcal U$ is bounded, $h$ has the max-structure (5.2)–(5.4) with $L_h=L_{uu}+L_{uv}^2/\rho$, $\bar L=2L_h$, and $(\hat h(u_t),\hat\nabla h(u_t))=(\bar\Psi(u_t,v_t),\nabla_u\bar\Psi(u_t,v_t))$ for all $t\ge0$, where $v_t\in\mathcal V$ and $h(u_t)-\bar\Psi(u_t,v_t)\le\delta_t/2$ (5.21), then
--   $$
--   \bar\Delta(z_t,\bar v_t)\ \le\ \frac{8L_h\Omega_{\omega_{\mathcal U}}(u_0)}{(t+2)^2}+\frac{\sum_{i=0}^t(i+2)^2\delta_i}{(t+2)^2},\qquad\forall t\ge0, \tag{5.25}
--   $$
--   where $\bar\Delta(u,v)=P(u)-\Xi(v)$ is the duality gap (5.6), $\bar v_t$ is the average (5.22), and $\Omega_{\omega_{\mathcal U}}(u_0):=\max_{u\in\mathcal U}D_{\omega_{\mathcal U}}(u,u_0)<+\infty$ (5.26).
--
--   The theorem extends the accelerated $O(1/t^2)$ rate of Nesterov's non-Hilbertian method to inexact first-order information, with the errors accumulating as the weighted sum displayed, and adds a duality-gap guarantee for bounded $\mathcal U$.
--
--   **Formalization Note** Both clauses concern the same run. In clause 2 the FOA property of the oracle is not assumed; it follows from (5.21) by Lemma 5.1. The duality gap is written against every point of the infimum defining $\Xi$, and the finiteness of $\Omega$ is part of the conclusion.
--
--   Differences from the source:
--   - generalization: ω_U is a DGF: continuous, 1-strongly convex on U and essentially smooth (continuously differentiable on int dom ω_U, gradient norm blowing up at the boundary) → ω_U continuous and 1-strongly convex on U and differentiable on an open convex set Wo standing for int dom ω_U; reason: the arguments use ∇ω_U only at points of U° = U ∩ Wo; essential smoothness serves only to place BPP solutions in U°, which the run (or the hypothesis on u⁺) states directly; every DGF of the page satisfies the Lean hypotheses
--   - encoding: ω_U : 𝕌 → ℝ ∪ {+∞}, U° = U ∩ int dom ω_U → ω : 𝕌 → ℝ whose values off U are unused, and U° = U ∩ Wo with Wo open and convex; reason: Lean convention; the interior of the domain of a convex function is open and convex, and only values on U enter
--   - generalization: ζ has an easily computable BPP on U with DGF ω_U (every subproblem (5.17) has a unique solution in U°) → no BPP hypothesis on ζ; the run supplies its own minimizers, each lying in U°; reason: the proofs use only the minimizers the run actually computes; under the page's BPP assumption those minimizers are unique and lie in U°, so every run of the page is a run of the Lean definition
--   - encoding: input L̄ ≥ L_h (presupposing L̄ > 0, since θ := μ/L̄ and the initial subproblem carries L̄D) → L̄ > 0 and L_h ≤ L̄ in the run; reason: a nondegeneracy condition the page presupposes; it excludes only the undefined case L̄ = 0
--   - encoding: "we can choose α₀ = 1 and α_t = … , and under such choices, we have …" → for every run of Algorithm 2 with those weights, the bounds hold; reason: the reading of "we can choose": the conclusion is asserted for the stated weights
--   - encoding: the oracle (5.12) returns a (δ_t, L̄)-FOA of h at u_t → the FOA property is a separate hypothesis ∀ t, IsFOA h U (δ_t) L̄ (u_t) (ĥ_t) (ĝ_t) of the primal clause; reason: Lean packaging: the duality-gap clause replaces it with the max-structure oracle and (5.21), from which the FOA property follows by Lemma 5.1
--   - encoding: u* an optimal solution of (5.1), P* = P(u*) → any u* ∈ U with P(u*) ≤ P(x) for all x ∈ U; reason: the same object
--   - encoding: Δ̄(z_t, v̄_t) = P(z_t) − Ξ(v̄_t) ≤ B with Ξ(v) = inf_{u∈U} Ψ̄(u,v) + ζ(u) + μω_U(u) → ∀ x ∈ U, P(z_t) − (Ψ̄(x, v̄_t) + ζ(x) + μω(x)) ≤ B; reason: equivalent to the page's inequality for an infimum over the nonempty set U, without a junk value for an infimum that is not bounded below
--   - encoding: Ω_{ω_U}(u₀) := max_{u∈U} D_{ω_U}(u,u₀) < +∞ (5.26) → Ω = sSup of {D(u,u₀) : u ∈ U}, and BddAbove of that set is part of the conclusion; reason: the page's claim "< +∞" is proved, not assumed, so the real supremum is not a junk value
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 24, Theorem 5.1, (5.23)–(5.26) (oracle (5.21)–(5.22), p. 23; proof Appendix G, pp. 39–43)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Supplement_Problem
import Definitions.Def_PDSmooth_Framework_Supplement_FOA
import Definitions.Def_PDSmooth_Framework_Supplement_Alg2

namespace PDSmooth.Framework.Supplement

open PDSmooth.Framework

/-- Theorem 5.1, p. 24 (the case `μ = 0`): for a run of Algorithm 2 with `α₀ = 1`,
`α_t = (2t + 3)/4` (`t ≥ 1`) (5.23):
(5.24) if the oracle outputs are `(δ_t, L̄)`-FOAs, then for every minimizer `u*` of `P` on `U` and
every `t ≥ 0`, `P(z_t) − P* ≤ 4L̄D(u*,u₀)/(t + 2)² + Σ_{i≤t}(i + 2)²δ_i/(t + 2)²`;
(5.25)–(5.26) if `U` is bounded, `h` has the max-structure with `L_h = L_uu + L_uv²/ρ`, `L̄ = 2L_h`, and
the oracle is `(Ψ̄(u_t,v_t), ∇_uΨ̄(u_t,v_t))` with `v_t ∈ V`, `h(u_t) − Ψ̄(u_t,v_t) ≤ δ_t/2` (5.21), then
`Ω(u₀) < +∞` and `Δ̄(z_t, v̄_t) = P(z_t) − Ξ(v̄_t) ≤ 8L_hΩ(u₀)/(t + 2)² + Σ_{i≤t}(i + 2)²δ_i/(t + 2)²`,
stated against every `x ∈ U` in the infimum defining `Ξ`. -/
theorem theorem_5_1 {UU VV : Type*} [NormedAddCommGroup UU] [NormedSpace ℝ UU] [FiniteDimensional ℝ UU]
    [NormedAddCommGroup VV] [NormedSpace ℝ VV] [FiniteDimensional ℝ VV]
    {U U' Wo : Set UU} {h ζ ω : UU → ℝ} {Lh μ : ℝ} (hS : Sec5Setting U U' Wo h ζ ω Lh μ)
    (hμ : μ = 0)
    (Lbar : ℝ) (α δ hhat : ℕ → ℝ) (ghat s : ℕ → UU →L[ℝ] ℝ) (u ubar z w : ℕ → UU)
    (hα0 : α 0 = 1) (hα : ∀ t : ℕ, 1 ≤ t → α t = (2 * (t : ℝ) + 3) / 4)
    (hrun : IsAlg2Run U Wo ζ ω μ Lh Lbar α δ hhat ghat s u ubar z w) :
    ((∀ t, IsFOA h U (δ t) Lbar (u t) (hhat t) (ghat t)) →
      ∀ ustar ∈ U, (∀ x ∈ U, Pobj h ζ ω μ ustar ≤ Pobj h ζ ω μ x) →
      ∀ t : ℕ, Pobj h ζ ω μ (z t) - Pobj h ζ ω μ ustar
        ≤ 4 * Lbar * bregman ω ustar (u 0) / ((t : ℝ) + 2) ^ 2
          + (∑ i ∈ Finset.range (t + 1), ((i : ℝ) + 2) ^ 2 * δ i) / ((t : ℝ) + 2) ^ 2) ∧
    (∀ (V V' : Set VV) (Ψ : UU → VV → ℝ) (Luu Luv ρv : ℝ) (v : ℕ → VV),
      MaxStructure U U' h V V' Ψ Luu Luv ρv → Lh = Luu + Luv ^ 2 / ρv →
      Bornology.IsBounded U → Lbar = 2 * Lh →
      (∀ t, v t ∈ V) → (∀ t, h (u t) - Ψ (u t) (v t) ≤ δ t / 2) →
      (∀ t, hhat t = Ψ (u t) (v t) ∧ ghat t = fderiv ℝ (fun y => Ψ y (v t)) (u t)) →
      BddAbove ((fun x => bregman ω x (u 0)) '' U) ∧
      ∀ t : ℕ, ∀ x ∈ U, Pobj h ζ ω μ (z t) - dualInner Ψ ζ ω μ (vbar α v t) x
        ≤ 8 * Lh * OmegaU ω U (u 0) / ((t : ℝ) + 2) ^ 2
          + (∑ i ∈ Finset.range (t + 1), ((i : ℝ) + 2) ^ 2 * δ i) / ((t : ℝ) + 2) ^ 2) := by sorry

end PDSmooth.Framework.Supplement
