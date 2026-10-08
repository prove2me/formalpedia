-- Prove2me | Theorems.Thm_WeakMFG_Existence_lemma_7_11
-- name    : WeakMFG.Existence.lemma_7_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:15:51.777428+00:00
-- url     : https://prove2.me/theorems/95747158-5bbe-4e99-8e36-b9ce6310b833
-- title:
--   Lemma 7.11 — under (E) and (C), (µ, ν) ↦ 𝔸(µ, ν) is upper hemicontinuous with closed convex values
-- statement:
--   Assume the standing assumptions (S), (E) and (C). Equip $\mathbb A$ with the distance
--   $$\|\alpha-\beta\|_{\mathbb A}=\mathbb E\int_0^T\|\alpha_t-\beta_t\|\,dt,$$
--   and let $\mathbb A(\mu,\nu)$ be the set (7.4) built from the solution $Z^{\mu,\nu}$ of the BSDE (7.1). Then the map $\mathcal Q\times\mathcal M\ni(\mu,\nu)\mapsto\mathbb A(\mu,\nu)\in2^{\mathbb A}$:
--
--   1. has convex values;
--   2. has closed values: if $\alpha^n\in\mathbb A(\mu,\nu)$, $\alpha\in\mathbb A$ and $\|\alpha^n-\alpha\|_{\mathbb A}\to0$, then $\alpha\in\mathbb A(\mu,\nu)$;
--   3. is upper hemicontinuous: if $(\mu^n,\nu^n)\to(\mu,\nu)$ in $\mathcal Q\times\mathcal M$, then
--   $$\sup_{\alpha^n\in\mathbb A(\mu^n,\nu^n)}\ \inf_{\alpha\in\mathbb A(\mu,\nu)}\|\alpha^n-\alpha\|_{\mathbb A}\to0 .$$
--
--   This is the hypothesis on $\Gamma$ in the fixed point theorem (Proposition 7.4), applied with $K=\mathcal Q\times\mathcal M$ and $E=\mathbb A$.
--
--   **Formalization Note** The $Z$-components of solutions of (7.1) at every $(\mu,\nu)\in\mathcal Q\times\mathcal M$ are a hypothesis (a solution map), not a choice. Closedness and upper hemicontinuity are stated with sequences, as the page proves them, and the sup–inf convergence is unfolded as "for every $\varepsilon>0$, eventually every $\alpha^n\in\mathbb A(\mu^n,\nu^n)$ has some $\alpha\in\mathbb A(\mu,\nu)$ with $\|\alpha^n-\alpha\|_{\mathbb A}<\varepsilon$". The distance is computed in $[0,\infty]$, and the maximizer sets are formed at an arbitrary $q_0\in\mathcal P(A)$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), Lemma 7.11, p. 27 (with ‖·‖_𝔸 defined just above it)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WeakMFG_Existence_Model
import Definitions.Def_WeakMFG_Existence_Hyp
import Definitions.Def_WeakMFG_Existence_Reward
import Definitions.Def_WeakMFG_Existence_FixedPoint

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Existence

/-- Lemma 7.11 (Carmona–Lacker, arXiv:1307.1152v2, p. 27): under (E) and (C), the set-valued map
`𝔸 : Q × M → 2^𝔸` of (7.4) is upper hemicontinuous and has closed and convex values, for the
distance `‖α − β‖_𝔸 = E ∫₀ᵀ ‖α_t − β_t‖ dt` on `𝔸`.
Formalization Notes: `Zsol μ ν` is the `Z`-component of a solution of the BSDE (7.1) at every
`(μ, ν) ∈ Q × M` (a hypothesis, never a choice); closedness and upper hemicontinuity are stated
sequentially, as the page proves them (p. 27: `sup_{αⁿ ∈ 𝔸(μⁿ,νⁿ)} inf_{α ∈ 𝔸(μ,ν)} ‖αⁿ − α‖_𝔸 → 0`,
unfolded); `‖·‖_𝔸` is an `ℝ≥0∞` integral; the maximizer set is taken at an arbitrary `q₀`. -/
theorem lemma_7_11 {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {ψ : Path d T → ℝ}
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    {A : Set EA} {Ω : Type*} [MeasurableSpace Ω] (B : Base d T Ω)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → Path d T)
    (hS : Standing B A ψ σ b f g X Xp)
    (hE : CondE B A ψ b f g Xp) (hC : CondC σ b f)
    (Ysol : Ppsi ψ → Mflow A → ℝ≥0 → Ω → Unit → ℝ)
    (Zsol : Ppsi ψ → Mflow A → Fin d → ℝ≥0 → Ω → Unit → ℝ)
    (hsol : ∀ μ ∈ Qset B A σ b Xp, ∀ ν : Mflow A,
      IsBSDE71 B σ b f g Xp μ ν (Ysol μ ν) (Zsol μ ν))
    (q₀ : PA A) :
    (∀ μ ∈ Qset B A σ b Xp, ∀ ν : Mflow A, Convex ℝ (Aopt B σ b f Xp μ (Zsol μ ν) q₀)) ∧
    (∀ μ ∈ Qset B A σ b Xp, ∀ ν : Mflow A, ∀ (αn : ℕ → ℝ≥0 → Ω → EA) (α : ℝ≥0 → Ω → EA),
      (∀ n, αn n ∈ Aopt B σ b f Xp μ (Zsol μ ν) q₀) → IsAdmissible B A α →
      Tendsto (fun n => ∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) T,
          ‖αn n t.toNNReal ω - α t.toNNReal ω‖ₑ ∂volume ∂B.P) atTop (𝓝 0) →
      α ∈ Aopt B σ b f Xp μ (Zsol μ ν) q₀) ∧
    (∀ (μn : ℕ → Ppsi ψ) (μ : Ppsi ψ) (νn : ℕ → Mflow A) (ν : Mflow A),
      (∀ n, μn n ∈ Qset B A σ b Xp) → μ ∈ Qset B A σ b Xp →
      Tendsto μn atTop (𝓝 μ) → StableTendsto T νn ν →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ αn ∈ Aopt B σ b f Xp (μn n) (Zsol (μn n) (νn n)) q₀,
          ∃ α ∈ Aopt B σ b f Xp μ (Zsol μ ν) q₀,
            ∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) T,
              ‖αn t.toNNReal ω - α t.toNNReal ω‖ₑ ∂volume ∂B.P < ENNReal.ofReal ε) := by sorry

end WeakMFG.Existence
