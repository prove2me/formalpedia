-- Prove2me | Theorems.Thm_StatComplexityDM_Disagreement_posterior_sampling_sq_dec_disagreement
-- name    : StatComplexityDM.Disagreement.posterior_sampling_sq_dec_disagreement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:23:22.695633+00:00
-- url     : https://prove2.me/theorems/aaca529e-943f-4126-b80a-4bd1edaf4489
-- title:
--   Theorem 6.2, (72), p. 45 — posterior sampling certifies dec^Sq_γ(µ, M̄) ≤ inf_{Δ>0}{2Δ + 24·sup_M θ(F_M − f^M, Δ, γ⁻¹; ρ_µ)·log²(γ)/γ} for γ ≥ e
-- statement:
--   Let $\mathcal{F}_{\mathcal{M}} \subseteq (\Pi \to [0, 1])$ be the class of mean-reward functions of a model class $\mathcal{M}$. Let $\mu = \sum_i w_i \delta_{M_i}$ be a finitely supported prior over $\mathcal{M}$, where each $M_i$ has mean reward $f^{M_i} \in \mathcal{F}_{\mathcal{M}}$ and optimal decision $\pi_{M_i} \in \arg\max_{\pi} f^{M_i}(\pi)$. Let $\overline{M}$ be a reference model, not necessarily in $\mathcal{M}$, with mean reward $f^{\overline{M}} : \Pi \to [0, 1]$. The **posterior sampling** strategy plays $\rho_\mu(\pi) := \mu(\{\pi_M = \pi\})$, the law of $\pi_M$ under $M \sim \mu$. Then for all $\gamma \ge e$ it certifies
--   $$
--   \underline{\mathrm{dec}}^{\mathrm{Sq}}_\gamma(\mu, \overline{M}) \le \inf_{\Delta > 0} \left\{ 2\Delta + 24\, \frac{\sup_{M\in\mathcal{M}} \theta(\mathcal{F}_{\mathcal{M}} - f^M, \Delta, \gamma^{-1}; \rho_\mu) \log^2(\gamma)}{\gamma} \right\},
--   $$
--   that is, the objective of (70),
--   $$
--   \mathbb{E}_{M\sim\mu}\, \mathbb{E}_{\pi\sim\rho_\mu}\Bigl[ f^M(\pi_M) - f^M(\pi) - \gamma \bigl(f^M(\pi) - f^{\overline{M}}(\pi)\bigr)^2 \Bigr],
--   $$
--   with $M \sim \mu$ and $\pi \sim \rho_\mu$ independent, is at most the right-hand side. Here $\theta$ is the disagreement coefficient of Definition 6.3.
--
--   Theorem 6.2 is a prior-dependent upper bound on the dual square-loss Decision-Estimation Coefficient. Combined with a bound of the disagreement coefficient by the star number or the eluder dimension (Lemma 6.1) and the minimax theorem, it yields the paper's Theorem 6.1, which recovers the eluder-dimension regret bound of Russo and Van Roy as a special case.
--
--   **Formalization Note** The infimum over $\Delta > 0$ is stated as a bound for every $\Delta > 0$, and the supremum over $M \in \mathcal{M}$ as a bound for every upper bound $\Theta$ of $\theta(\mathcal{F}_{\mathcal{M}} - g, \Delta, \gamma^{-1}; \rho_\mu)$ over all $g \in \mathcal{F}_{\mathcal{M}}$; both forms are equivalent to the page's and avoid Lean's default values for empty or unbounded infima and suprema. The bound is stated for the posterior sampling distribution itself, which upper-bounds the infimum over $p$ in (70). Priors and $\rho_\mu$ are finite weighted families (footnote 5 of the paper); models enter only through their mean rewards and optimal decisions, which is all the square-loss DEC depends on. $\log$ is the natural logarithm and $e = \exp(1)$.
-- source:
--   arXiv:2112.13487v3, Theorem 6.2, (72), p. 45 (proof p. 106)

import Mathlib
import Definitions.Def_StatComplexityDM_Disagreement_Coefficient

namespace StatComplexityDM.Disagreement

/-- Theorem 6.2, (72), p. 45 (arXiv:2112.13487v3). For a class `F_M ⊆ (Π → [0, 1])` of mean-reward
functions, a finitely supported prior `µ = Σ_i w i · δ_{M_i}` over models with `fM i = f^{M_i} ∈ F_M`
and `piM i = π_{M_i} ∈ arg max f^{M_i}`, and a reference model `M̄` (not necessarily in `M`) with
`fbar = f^{M̄} ∈ [0, 1]`, the posterior sampling strategy `ρ_µ(π) = µ({π_M = π})` (the weighted
family `Σ_j w j · δ_{piM j}`) certifies, for all `γ ≥ e`,
`dec^Sq_γ(µ, M̄) ≤ inf_{Δ>0} {2Δ + 24 sup_{M∈M} θ(F_M − f^M, Δ, γ⁻¹; ρ_µ) log²(γ)/γ}`:
the objective of (70) at `p = ρ_µ` is at most `2Δ + 24Θ log²(γ)/γ` for every `Δ > 0` and every
upper bound `Θ` of `θ(F_M − g, Δ, γ⁻¹; ρ_µ)` over all `g = f^M ∈ F_M`. -/
theorem posterior_sampling_sq_dec_disagreement {ι Act : Type*} [Fintype ι] (FM : Set (Act → ℝ))
    (hF : ∀ f ∈ FM, ∀ π, 0 ≤ f π ∧ f π ≤ 1) (w : ι → ℝ) (hw : StatComplexityDM.LowerBound.IsDist w) (fM : ι → Act → ℝ)
    (hfM : ∀ i, fM i ∈ FM) (piM : ι → Act) (hpiM : ∀ i π, fM i π ≤ fM i (piM i))
    (fbar : Act → ℝ) (hfbar : ∀ π, 0 ≤ fbar π ∧ fbar π ≤ 1) (γ : ℝ) (hγ : Real.exp 1 ≤ γ) :
    ∀ Δ : ℝ, 0 < Δ → ∀ Θ : ℝ,
      (∀ g ∈ FM, disagreementCoeff (shiftClass FM g) Δ γ⁻¹ w piM ≤ Θ) →
      sqDecObjective w fM piM fbar γ w piM ≤ 2 * Δ + 24 * Θ * Real.log γ ^ 2 / γ := by sorry

end StatComplexityDM.Disagreement
