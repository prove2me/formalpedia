-- Prove2me | Theorems.Thm_StatComplexityDM_Disagreement_ps_fixed_shift_bound
-- name    : StatComplexityDM.Disagreement.ps_fixed_shift_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:59.31223+00:00
-- url     : https://prove2.me/theorems/ecdee286-9036-4357-bf0c-1e786ea91838
-- title:
--   Theorem 6.2 (proof), p. 106 — Lemma E.2 for F_M − f^{M̃} at γ/4: E_µ[f^M(π_M) − f^{M̃}(π_M)] ≤ 2Δ + 24θ log²(γ ∨ e)/γ + (γ/4)E[(f^M − f^{M̃})²]
-- statement:
--   Let $\mathcal{F}_{\mathcal{M}}$ be a class of mean-reward functions $\Pi \to [0, 1]$, and let $\mu = \sum_i w_i \delta_{M_i}$ be a finitely supported prior over models with $f^{M_i} \in \mathcal{F}_{\mathcal{M}}$ and $\pi_{M_i} \in \arg\max_{\pi} f^{M_i}(\pi)$. Let $p = \rho_\mu$, $\rho_\mu(\pi) := \mu(\{\pi_M = \pi\})$, be the posterior sampling distribution. Fix a model $\widetilde{M}$ with $f^{\widetilde{M}} \in \mathcal{F}_{\mathcal{M}}$, and let $\gamma \ge e$. Then for every $\Delta > 0$,
--   $$
--   \mathbb{E}_{M\sim\mu}\bigl[f^M(\pi_M) - f^{\widetilde{M}}(\pi_M)\bigr] \le 2\Delta + 24\, \frac{\theta(\mathcal{F}_{\mathcal{M}} - f^{\widetilde{M}}, \Delta, \gamma^{-1}; \rho_\mu) \log^2(\gamma \vee e)}{\gamma} + \frac{\gamma}{4} \cdot \mathbb{E}_{\pi\sim p,\, M\sim\mu}\Bigl[\bigl(f^M(\pi) - f^{\widetilde{M}}(\pi)\bigr)^2\Bigr],
--   $$
--   where $\pi \sim p$ and $M \sim \mu$ are independent and $\theta$ is the disagreement coefficient of Definition 6.3.
--
--   This is Lemma E.2 applied to the shifted class $\mathcal{F}_{\mathcal{M}} - f^{\widetilde{M}} \subseteq (\Pi \to [-1, 1])$ with parameter $\gamma/4$; averaging it over $\widetilde{M} \sim \mu$ gives Theorem 6.2.
--
--   **Formalization Note** The infimum over $\Delta > 0$ is stated as a bound for every $\Delta > 0$. The prior and $\rho_\mu$ are finite weighted families; models enter only through their mean rewards and decisions. The page derives this display inside the proof of Theorem 6.2, whose standing range is $\gamma \ge e$.
-- source:
--   arXiv:2112.13487v3, App. E.2.2, proof of Theorem 6.2, p. 106 ("We now apply Lemma E.2 with the class F_M − f^M̃ and parameter γ/4")

import Mathlib
import Definitions.Def_StatComplexityDM_Disagreement_Coefficient

namespace StatComplexityDM.Disagreement

/-- Proof of Theorem 6.2, p. 106 (arXiv:2112.13487v3), Lemma E.2 applied with the class `F_M − f^{M̃}`
and parameter `γ/4`: for a class `F_M ⊆ (Π → [0, 1])`, a finitely supported prior
`µ = Σ_i w i · δ_{M_i}` with `fM i = f^{M_i} ∈ F_M` and `piM i = π_{M_i}`, posterior sampling
`p = ρ_µ = Σ_j w j · δ_{piM j}`, a fixed `M̃ ∈ M` with mean reward `g = f^{M̃} ∈ F_M`, `γ ≥ e` and
every `Δ > 0`,
`E_{M∼µ}[f^M(π_M) − f^{M̃}(π_M)] ≤ 2Δ + 24 θ(F_M − f^{M̃}, Δ, γ⁻¹; ρ_µ) log²(γ ∨ e)/γ
  + (γ/4) · E_{π∼p, M∼µ}[(f^M(π) − f^{M̃}(π))²]`. -/
theorem ps_fixed_shift_bound {ι Act : Type*} [Fintype ι] (FM : Set (Act → ℝ))
    (hF : ∀ f ∈ FM, ∀ π, 0 ≤ f π ∧ f π ≤ 1) (w : ι → ℝ) (hw : StatComplexityDM.LowerBound.IsDist w) (fM : ι → Act → ℝ)
    (hfM : ∀ i, fM i ∈ FM) (piM : ι → Act) (hpiM : ∀ i π, fM i π ≤ fM i (piM i))
    (g : Act → ℝ) (hg : g ∈ FM) (γ : ℝ) (hγ : Real.exp 1 ≤ γ) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∑ i, w i * (fM i (piM i) - g (piM i))
      ≤ 2 * Δ + 24 * disagreementCoeff (shiftClass FM g) Δ γ⁻¹ w piM
          * Real.log (max γ (Real.exp 1)) ^ 2 / γ
        + γ / 4 * ∑ j, w j * ∑ i, w i * (fM i (piM j) - g (piM j)) ^ 2 := by sorry

end StatComplexityDM.Disagreement
