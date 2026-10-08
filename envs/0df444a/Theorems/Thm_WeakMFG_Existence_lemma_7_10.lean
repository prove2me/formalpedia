-- Prove2me | Theorems.Thm_WeakMFG_Existence_lemma_7_10
-- name    : WeakMFG.Existence.lemma_7_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:16:01.895988+00:00
-- url     : https://prove2.me/theorems/732551db-46b7-4033-8c51-6be007c6c253
-- title:
--   Lemma 7.10 — Z^{µⁿ,νⁿ} → Z^{µ,ν} in L²(dt × dP) when (µⁿ, νⁿ) → (µ, ν) in Q × M
-- statement:
--   Assume the standing assumptions (S) and assumption (E). Suppose $(\mu^n,\nu^n)\to(\mu,\nu)$ in $\mathcal Q\times\mathcal M$, using $\tau_\psi(\mathcal C)$ on $\mathcal Q$ and the stable topology on $\mathcal M$, and let $(Y^{\mu^n,\nu^n},Z^{\mu^n,\nu^n})$ and $(Y^{\mu,\nu},Z^{\mu,\nu})$ solve the BSDE (7.1). Then
--   $$\lim_{n\to\infty}\mathbb E\Big[\int_0^T\big|Z^{\mu^n,\nu^n}_t-Z^{\mu,\nu}_t\big|^2dt\Big]=0.$$
--
--   This continuity of the adjoint process in $(\mu,\nu)$ is what makes the optimal-control sets depend upper hemicontinuously on $(\mu,\nu)$ (Lemma 7.11).
--
--   **Formalization Note** The BSDE solutions are hypotheses. Convergence in $\mathcal M$ is stable convergence along the sequence. $|\cdot|^2$ is the Euclidean square written as a sum of coordinates, and the expectation is computed in $[0,\infty]$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), Lemma 7.10, p. 25

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WeakMFG_Existence_Model
import Definitions.Def_WeakMFG_Existence_Hyp
import Definitions.Def_WeakMFG_Existence_Reward
import Definitions.Def_WeakMFG_Existence_FixedPoint

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Existence

/-- Lemma 7.10 (Carmona–Lacker, arXiv:1307.1152v2, p. 25): suppose (E). Suppose
`(μⁿ, νⁿ) → (μ, ν)` in `Q × M`, using `τ_ψ(C)` on `Q`. Then
`lim_n E[∫₀ᵀ |Z^{μⁿ,νⁿ}_t − Z^{μ,ν}_t|² dt] = 0`.
Formalization Notes: the solutions of the BSDE (7.1) at `(μⁿ, νⁿ)` and `(μ, ν)` are hypotheses;
convergence in `M` is stable convergence along the sequence; `|·|²` is the Euclidean square,
written as a coordinate sum, and the expectation is an `ℝ≥0∞` integral. -/
theorem lemma_7_10 {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {ψ : Path d T → ℝ}
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    {A : Set EA} {Ω : Type*} [MeasurableSpace Ω] (B : Base d T Ω)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → Path d T)
    (hS : Standing B A ψ σ b f g X Xp)
    (hE : CondE B A ψ b f g Xp)
    (μn : ℕ → Ppsi ψ) (μ : Ppsi ψ) (hμn : ∀ n, μn n ∈ Qset B A σ b Xp) (hμ : μ ∈ Qset B A σ b Xp)
    (hμconv : Tendsto μn atTop (𝓝 μ))
    (νn : ℕ → Mflow A) (ν : Mflow A) (hνconv : StableTendsto T νn ν)
    (Yn : ℕ → ℝ≥0 → Ω → Unit → ℝ) (Zn : ℕ → Fin d → ℝ≥0 → Ω → Unit → ℝ)
    (Y : ℝ≥0 → Ω → Unit → ℝ) (Z : Fin d → ℝ≥0 → Ω → Unit → ℝ)
    (hYZn : ∀ n, IsBSDE71 B σ b f g Xp (μn n) (νn n) (Yn n) (Zn n))
    (hYZ : IsBSDE71 B σ b f g Xp μ ν Y Z) :
    Tendsto (fun n => ∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) T,
        ∑ j, ‖Zn n j t.toNNReal ω () - Z j t.toNNReal ω ()‖ₑ ^ 2 ∂volume ∂B.P)
      atTop (𝓝 0) := by sorry

end WeakMFG.Existence
