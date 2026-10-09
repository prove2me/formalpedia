-- Prove2me | Theorems.Thm_StatComplexityDM_Disagreement_decoupling_unit_scale
-- name    : StatComplexityDM.Disagreement.decoupling_unit_scale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:23:30.759729+00:00
-- url     : https://prove2.me/theorems/5fccce2d-59b5-4a2d-bd59-1525f0c7e458
-- title:
--   Lemma E.2 (proof), p. 105 — for F ⊆ (Π → [−1,1]): E|f_z(π_z)| ≤ Δ + ηε²/2 + (4θ log(1/ε) log(1/Δ) + 1)/(2η) + (η/2)E[f_z²(π_z′)]
-- statement:
--   Let $\mathcal{Z}$ be a finite index set with a distribution $\mu \in \Delta(\mathcal{Z})$, let $\mathcal{F}$ be a class of functions $\Pi \to [-1, 1]$, and let $\{f_z\}_{z\in\mathcal{Z}} \subseteq \mathcal{F}$ and $\{\pi_z\}_{z\in\mathcal{Z}} \subseteq \Pi$. Write $\rho_\mu(\pi) := \mu(\{\pi_z = \pi\})$ for the law of $\pi_z$ under $z \sim \mu$. Then for all $\Delta \in (0, 1]$, $\varepsilon \in (0, 1]$ and $\eta > 0$,
--   $$
--   \mathbb{E}_{z\sim\mu}\bigl[|f_z(\pi_z)|\bigr] \le \Delta + \frac{\eta\varepsilon^2}{2} + \frac{1}{2\eta}\Bigl(4\,\theta(\mathcal{F}, \Delta, \varepsilon; \rho_\mu) \log(1/\varepsilon) \log(1/\Delta) + 1\Bigr) + \frac{\eta}{2}\, \mathbb{E}_{z, z'\sim\mu}\bigl[f_z^2(\pi_{z'})\bigr],
--   $$
--   where $z, z'$ are independent draws from $\mu$ and $\theta$ is the disagreement coefficient of Definition 6.3.
--
--   This is the unit-scale form of the decoupling lemma, before the parameters $\eta$, $\varepsilon$ are tuned and the range is rescaled to $[-R, R]$.
--
--   **Formalization Note** The distribution $\mu$ is a finite weighted family; $\log$ is the natural logarithm.
-- source:
--   arXiv:2112.13487v3, App. E.2.1, proof of Lemma E.2, p. 105 ("Altogether, we have")

import Mathlib
import Definitions.Def_StatComplexityDM_Disagreement_Coefficient

namespace StatComplexityDM.Disagreement

/-- Proof of Lemma E.2, p. 105, the bound "Altogether, we have" (arXiv:2112.13487v3): for a
class `F ⊆ (Π → [−1, 1])`, a finitely supported `µ = Σ_i w i · δ_{z_i}` on an index set,
`f_z = fz i ∈ F`, `π_z = πz i`, `ρ_µ = Σ_i w i · δ_{πz i}`, and all `Δ ∈ (0, 1]`, `ε ∈ (0, 1]`,
`η > 0`:
`E_{z∼µ}[|f_z(π_z)|] ≤ Δ + ηε²/2 + (1/(2η))(4θ(F, Δ, ε; ρ_µ) log(1/ε) log(1/Δ) + 1)
  + (η/2) E_{z,z′∼µ}[f_z²(π_{z′})]`. -/
theorem decoupling_unit_scale {ι Act : Type*} [Fintype ι] (F : Set (Act → ℝ))
    (hF : ∀ f ∈ F, ∀ π, |f π| ≤ 1) (w : ι → ℝ) (hw : StatComplexityDM.LowerBound.IsDist w) (fz : ι → Act → ℝ)
    (hfz : ∀ i, fz i ∈ F) (πz : ι → Act) (Δ ε η : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    ∑ i, w i * |fz i (πz i)|
      ≤ Δ + η * ε ^ 2 / 2
        + 1 / (2 * η) * (4 * disagreementCoeff F Δ ε w πz * Real.log (1 / ε) * Real.log (1 / Δ) + 1)
        + η / 2 * ∑ i, w i * ∑ j, w j * fz i (πz j) ^ 2 := by sorry

end StatComplexityDM.Disagreement
