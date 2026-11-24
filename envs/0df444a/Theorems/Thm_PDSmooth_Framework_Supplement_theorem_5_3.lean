-- Prove2me | Theorems.Thm_PDSmooth_Framework_Supplement_theorem_5_3
-- name    : PDSmooth.Framework.Supplement.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:58:04.080644+00:00
-- url     : https://prove2.me/theorems/451c4dea-62ab-4b7d-8ba3-e152978dffb2
-- title:
--   Theorem 5.3, p. 26 — adaptive stopping test for Algorithm 2 (μ > 0): (5.39) implies P(w_{t+1}) − P* ≤ ϵ
-- statement:
--   Assume the standing assumptions of §5 with $\mu>0$ and consider a run of Algorithm 2. For $t\ge0$ let
--
--   $$
--   e(u_{t+1}):=\hat\nabla h(u_{t+1})-\nabla h(u_{t+1}), \tag{5.37}
--   $$
--
--   $$
--   G_t:=L_h(w_{t+1}-u_{t+1})\quad\text{and}\quad\bar G_t:=(A_t\mu+\bar L)\alpha_{t+1}^{-1}\big(\nabla\omega_{\mathcal U}(\bar u_{t+1})-\nabla\omega_{\mathcal U}(w_{t+1})\big). \tag{5.38}
--   $$
--
--   Then for any $t\ge0$ and $\epsilon$, if
--
--   $$
--   \|\bar G_t\|_*^2+\|G_t\|^2\le\mu\epsilon/3\qquad\text{and}\qquad\|e(u_{t+1})\|_*\le\sqrt{\mu\epsilon/3}, \tag{5.39}
--   $$
--
--   then $P(w_{t+1})-P^*\le\epsilon$.
--
--   The test uses only quantities that Algorithm 2 already computes, so it can certify $\epsilon$-optimality of $w_{t+1}$ before the worst-case iteration count of Corollary 5.1 is reached, and without knowing $D_{\omega_{\mathcal U}}(u^*,u_0)$.
--
--   **Formalization Note** The theorem holds for every run, with any positive weights and any oracle values $\hat\nabla h(u_{t+1})$; the FOA property is not used.
--
--   Differences from the source:
--   - generalization: ω_U is a DGF: continuous, 1-strongly convex on U and essentially smooth (continuously differentiable on int dom ω_U, gradient norm blowing up at the boundary) → ω_U continuous and 1-strongly convex on U and differentiable on an open convex set Wo standing for int dom ω_U; reason: the arguments use ∇ω_U only at points of U° = U ∩ Wo; essential smoothness serves only to place BPP solutions in U°, which the run (or the hypothesis on u⁺) states directly; every DGF of the page satisfies the Lean hypotheses
--   - encoding: ω_U : 𝕌 → ℝ ∪ {+∞}, U° = U ∩ int dom ω_U → ω : 𝕌 → ℝ whose values off U are unused, and U° = U ∩ Wo with Wo open and convex; reason: Lean convention; the interior of the domain of a convex function is open and convex, and only values on U enter
--   - generalization: ζ has an easily computable BPP on U with DGF ω_U (every subproblem (5.17) has a unique solution in U°) → no BPP hypothesis on ζ; the run supplies its own minimizers, each lying in U°; reason: the proofs use only the minimizers the run actually computes; under the page's BPP assumption those minimizers are unique and lie in U°, so every run of the page is a run of the Lean definition
--   - encoding: input L̄ ≥ L_h (presupposing L̄ > 0, since θ := μ/L̄ and the initial subproblem carries L̄D) → L̄ > 0 and L_h ≤ L̄ in the run; reason: a nondegeneracy condition the page presupposes; it excludes only the undefined case L̄ = 0
--   - encoding: P(·) − P* with P* = min_{u∈U} P(u) → P(·) − P(x) for every x ∈ U; reason: equivalent to the bound on P(·) − P* for the minimum P*, and needs no separate minimizer
--   - generalization: in Algorithm 2 (whose oracle (5.12) returns (δ_t, L̄)-FOAs) → any run of the recursion, with arbitrary oracle values ĥ_t, ĝ_t; reason: the proof uses only (5.14) and the definition (5.37) of the error; runs of the page are runs of the Lean definition
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 26, Theorem 5.3, (5.37)–(5.39)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Supplement_Problem
import Definitions.Def_PDSmooth_Framework_Supplement_Alg2

namespace PDSmooth.Framework.Supplement

/-- Theorem 5.3, p. 26 (§5.4, `μ > 0`): for a run of Algorithm 2 and any `t ≥ 0`, with
`e(u_{t+1}) = ĝ_{t+1} − ∇h(u_{t+1})` (5.37), `G_t = L_h(w_{t+1} − u_{t+1})` and
`Ḡ_t = (A_tμ + L̄)α_{t+1}⁻¹(∇ω(ū_{t+1}) − ∇ω(w_{t+1}))` (5.38): if `‖Ḡ_t‖²_* + ‖G_t‖² ≤ μϵ/3` and
`‖e(u_{t+1})‖_* ≤ √(μϵ/3)` (5.39), then `P(w_{t+1}) − P* ≤ ϵ`; `P*` is the minimum of `P` on `U`, and
the bound is stated against every `x ∈ U`. -/
theorem theorem_5_3 {UU : Type*} [NormedAddCommGroup UU] [NormedSpace ℝ UU] [FiniteDimensional ℝ UU]
    {U U' Wo : Set UU} {h ζ ω : UU → ℝ} {Lh μ : ℝ} (hS : Sec5Setting U U' Wo h ζ ω Lh μ)
    (hμ : 0 < μ)
    (Lbar : ℝ) (α δ hhat : ℕ → ℝ) (ghat s : ℕ → UU →L[ℝ] ℝ) (u ubar z w : ℕ → UU)
    (hrun : IsAlg2Run U Wo ζ ω μ Lh Lbar α δ hhat ghat s u ubar z w) (ε : ℝ) :
    ∀ t : ℕ,
      ‖((accW α t * μ + Lbar) * (α (t + 1))⁻¹) • (fderiv ℝ ω (ubar (t + 1)) - fderiv ℝ ω (w (t + 1)))‖ ^ 2
          + ‖Lh • (w (t + 1) - u (t + 1))‖ ^ 2 ≤ μ * ε / 3 →
      ‖ghat (t + 1) - fderiv ℝ h (u (t + 1))‖ ≤ Real.sqrt (μ * ε / 3) →
      ∀ x ∈ U, Pobj h ζ ω μ (w (t + 1)) - Pobj h ζ ω μ x ≤ ε := by sorry

end PDSmooth.Framework.Supplement
