-- Prove2me | Theorems.Thm_StatComplexityDM_Disagreement_decoupling_disagreement
-- name    : StatComplexityDM.Disagreement.decoupling_disagreement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:23:08.11854+00:00
-- url     : https://prove2.me/theorems/b0c985bb-a2b6-4373-94ba-d168f6dff810
-- title:
--   Lemma E.2, (140), p. 104 — E|f_z(π_z)| ≤ 2Δ + 6θ(F, Δ, γ⁻¹; ρ_µ) log²(Rγ ∨ e)/γ + γ·E[f_z²(π_z′)], for R ≥ 1
-- statement:
--   Let $\mathcal{Z}$ be a finite index set with a distribution $\mu \in \Delta(\mathcal{Z})$, let $R \ge 1$ and let $\mathcal{F}$ be a class of functions $\Pi \to [-R, R]$. Let $\{f_z\}_{z\in\mathcal{Z}} \subseteq \mathcal{F}$ and $\{\pi_z\}_{z\in\mathcal{Z}} \subseteq \Pi$, and let $\rho_\mu(\pi) := \mu(\{\pi_z = \pi\})$. Then for all $\gamma > 0$,
--   $$
--   \mathbb{E}_{z\sim\mu}\bigl[|f_z(\pi_z)|\bigr] \le \inf_{\Delta > 0} \left\{ 2\Delta + 6\, \frac{\theta(\mathcal{F}, \Delta, \gamma^{-1}; \rho_\mu) \log^2(R\gamma \vee e)}{\gamma} \right\} + \gamma \cdot \mathbb{E}_{z, z'\sim\mu}\bigl[f_z^2(\pi_{z'})\bigr],
--   $$
--   where $z, z'$ are independent draws from $\mu$ and $\theta$ is the disagreement coefficient of Definition 6.3.
--
--   The lemma decouples the random function $f_z$ from the random decision $\pi_z$: the coupled quantity on the left is controlled by the decoupled second moment on the right at the price of the disagreement coefficient. It is the engine of the posterior-sampling bound of Theorem 6.2.
--
--   **Formalization Note** The infimum over $\Delta > 0$ is stated as a bound for every $\Delta > 0$, which is equivalent. The page states the lemma for every $R$; its proof treats $R = 1$ and extends to every $R \ge 1$ by rescaling, which does not cover $R < 1$, so the statement here assumes $R \ge 1$ (Theorem 6.2 uses $R = 1$). The distribution $\mu$ is a finite weighted family; $\log$ is the natural logarithm and $e = \exp(1)$.
-- source:
--   arXiv:2112.13487v3, Lemma E.2, (140), p. 104 (proof pp. 104–106)

import Mathlib
import Definitions.Def_StatComplexityDM_Disagreement_Coefficient

namespace StatComplexityDM.Disagreement

/-- Lemma E.2, (140), p. 104 (arXiv:2112.13487v3), for `R ≥ 1`: for a finitely supported
`µ = Σ_i w i · δ_{z_i}` on an index set, a class `F ⊆ (Π → [−R, R])`, `f_z = fz i ∈ F`, `π_z = πz i`
and `ρ_µ(π) = µ({π_z = π})` (the weighted family `Σ_i w i · δ_{πz i}`), for all `γ > 0` and `Δ > 0`,
`E_{z∼µ}[|f_z(π_z)|] ≤ 2Δ + 6θ(F, Δ, γ⁻¹; ρ_µ) log²(Rγ ∨ e)/γ + γ · E_{z,z′∼µ}[f_z²(π_{z′})]`.
The infimum over `Δ > 0` of (140) is expressed as "for every `Δ > 0`". -/
theorem decoupling_disagreement {ι Act : Type*} [Fintype ι] (F : Set (Act → ℝ)) (R : ℝ)
    (hR : 1 ≤ R) (hF : ∀ f ∈ F, ∀ π, |f π| ≤ R) (w : ι → ℝ) (hw : StatComplexityDM.LowerBound.IsDist w)
    (fz : ι → Act → ℝ) (hfz : ∀ i, fz i ∈ F) (πz : ι → Act) (γ : ℝ) (hγ : 0 < γ)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    ∑ i, w i * |fz i (πz i)|
      ≤ 2 * Δ + 6 * disagreementCoeff F Δ γ⁻¹ w πz * Real.log (max (R * γ) (Real.exp 1)) ^ 2 / γ
        + γ * ∑ i, w i * ∑ j, w j * fz i (πz j) ^ 2 := by sorry

end StatComplexityDM.Disagreement
