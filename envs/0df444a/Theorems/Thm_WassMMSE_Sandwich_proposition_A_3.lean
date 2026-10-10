-- Prove2me | Theorems.Thm_WassMMSE_Sandwich_proposition_A_3
-- name    : WassMMSE.Sandwich.proposition_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:12.201469+00:00
-- url     : https://prove2.me/theorems/db0cceb4-ea94-48ff-b0bb-9b907a5736a2
-- title:
--   Proposition A.3, pp. 37–38 — closed form of sup_{Σ⪰0} ⟨D,Σ⟩ − γ Tr[Σ − 2(Σ̂^{1/2}ΣΣ̂^{1/2})^{1/2}] and its maximizer
-- statement:
--   Let $D\in\mathbb S^d$ be symmetric, $\widehat\Sigma\in\mathbb S^d_+$ and $\gamma\ge0$, and consider the nonlinear semidefinite program (A.3)
--   $$J^\star=\sup_{\Sigma\succeq0}\ \langle D,\Sigma\rangle-\gamma\operatorname{Tr}\big[\Sigma-2(\widehat\Sigma^{1/2}\Sigma\widehat\Sigma^{1/2})^{1/2}\big].$$
--   Then
--   $$J^\star=\begin{cases}\gamma^2\langle(\gamma I_d-D)^{-1},\widehat\Sigma\rangle & \text{if }\gamma>\lambda_{\max}(D),\\ \liminf_{\bar\gamma\downarrow\gamma}\bar\gamma^2\langle(\bar\gamma I_d-D)^{-1},\widehat\Sigma\rangle & \text{if }\gamma=\lambda_{\max}(D),\\ +\infty & \text{if }\gamma<\lambda_{\max}(D).\end{cases}$$
--   Moreover, if $\gamma>\lambda_{\max}(D)$, then $\Sigma^\star=\gamma^2(\gamma I_d-D)^{-1}\widehat\Sigma(\gamma I_d-D)^{-1}$ is positive semidefinite and attains $J^\star$, and if in addition $\widehat\Sigma\succ0$, it is the only positive semidefinite matrix that attains $J^\star$.
--
--   The proposition gives the inner supremum of the Lagrangian dual of the Gelbrich-constrained problems that appear throughout the paper; it is used to evaluate the worst case over a Gelbrich ball in closed form.
--
--   **Formalization Note** $J^\star$ is an `EReal` supremum, so the value $+\infty$ is representable, and the $\liminf$ is `Filter.liminf` along the right neighbourhood filter of $\gamma$, computed in `EReal`. $\lambda_{\max}$ is the mission's `lamMax`, which is $0$ at $d=0$; in that degenerate case every clause holds trivially.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 37, (A.3) and Proposition A.3; p. 38 (solution sentence)

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_psdSqrt
import Definitions.Def_WassMMSE_Sandwich_Programs

open Matrix Topology WassersteinDRO.Gelbrich

namespace WassMMSE.Sandwich

/-- Proposition A.3 (Nguyen et al., arXiv:1911.03539v2, p. 37–38): closed form of the nonlinear SDP
(A.3) `J⋆ = sup_{Σ⪰0} ⟨D, Σ⟩ − γ Tr[Σ − 2(Σ̂^{1/2} Σ Σ̂^{1/2})^{1/2}]` for `D ∈ 𝕊^d`, `Σ̂ ∈ 𝕊^d_+`,
`γ ≥ 0`; its maximizer `Σ⋆ = γ²(γI_d − D)⁻¹Σ̂(γI_d − D)⁻¹` for `γ > λ_max(D)`, unique when `Σ̂ ≻ 0`.
`λ_max(D)` is `lamMax D` (`0` at `d = 0`, where every clause holds trivially). -/
theorem proposition_A_3 {d : ℕ} (D Sh : Matrix (Fin d) (Fin d) ℝ) (hD : D.IsHermitian)
    (hSh : Sh.PosSemidef) (γ : ℝ) (hγ : 0 ≤ γ) :
    let J : Matrix (Fin d) (Fin d) ℝ → ℝ := fun S =>
      frob D S - γ * (S - (2 : ℝ) • psdSqrt (psdSqrt Sh * S * psdSqrt Sh)).trace
    let Jstar : EReal := ⨆ (S : Matrix (Fin d) (Fin d) ℝ) (_ : S.PosSemidef), (J S : EReal)
    let val : ℝ → ℝ := fun g => g ^ 2 * frob (g • (1 : Matrix (Fin d) (Fin d) ℝ) - D)⁻¹ Sh
    let Sstar : Matrix (Fin d) (Fin d) ℝ :=
      γ ^ 2 • ((γ • (1 : Matrix (Fin d) (Fin d) ℝ) - D)⁻¹ * Sh *
        (γ • (1 : Matrix (Fin d) (Fin d) ℝ) - D)⁻¹)
    (lamMax D < γ → Jstar = (val γ : EReal)) ∧
    (γ = lamMax D → Jstar = Filter.liminf (fun g : ℝ => (val g : EReal)) (𝓝[>] γ)) ∧
    (γ < lamMax D → Jstar = ⊤) ∧
    (lamMax D < γ →
      Sstar.PosSemidef ∧ (J Sstar : EReal) = Jstar ∧
      (Sh.PosDef → ∀ S : Matrix (Fin d) (Fin d) ℝ, S.PosSemidef → (J S : EReal) = Jstar →
        S = Sstar)) := by sorry

end WassMMSE.Sandwich
