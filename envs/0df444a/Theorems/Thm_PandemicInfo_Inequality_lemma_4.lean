-- Prove2me | Theorems.Thm_PandemicInfo_Inequality_lemma_4
-- name    : PandemicInfo.Inequality.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:08.105255+00:00
-- url     : https://prove2.me/theorems/7eb312e3-72a0-4f4d-a757-4498c53d42bc
-- title:
--   Lemma 4, p. 19 (PDF 20) — the lower convex envelope $k_\lambda$ of $\tilde K_\lambda$ by regime, (36)
-- statement:
--   **Lemma 4.** For $\mu\in[\omega_\ell,\omega_h]$ the lower convex envelope $k_\lambda$ of $\tilde K_\lambda$ on $[\omega_\ell,\omega_h]$ is
--
--   $$k_\lambda(\mu)=\begin{cases}\tilde K_\lambda(\omega_\ell)+\frac{\mu-\omega_\ell}{\omega_h-\omega_\ell}[\tilde K_\lambda(\omega_h)-\tilde K_\lambda(\omega_\ell)] & \text{if }\mathrm{FD}_1\vee\mathrm{FD}_2\vee\mathrm{FD}_3,\\ \tilde K_\lambda(\mu) & \text{if }\mathrm{ND}_1\vee\mathrm{ND}_2,\\ \tilde K_\lambda(\mu)\mathbb 1_{\{\mu\le\mu^{DP}_\lambda\}}+\Big[\tilde K_\lambda(\mu^{DP}_\lambda)+(\mu-\mu^{DP}_\lambda)\frac{\tilde K_\lambda(\omega_h)-\tilde K_\lambda(\mu^{DP}_\lambda)}{\omega_h-\mu^{DP}_\lambda}\Big]\mathbb 1_{\{\mu>\mu^{DP}_\lambda\}} & \text{if DP},\\ \tilde K_\lambda(\mu)\mathbb 1_{\{\mu\ge\mu^{EX}_\lambda\}}+\Big[\tilde K_\lambda(\omega_\ell)+(\mu-\omega_\ell)\frac{\tilde K_\lambda(\mu^{EX}_\lambda)-\tilde K_\lambda(\omega_\ell)}{\mu^{EX}_\lambda-\omega_\ell}\Big]\mathbb 1_{\{\mu<\mu^{EX}_\lambda\}} & \text{if EX},\end{cases}$$
--
--   with the regimes (29)–(35).
--
--   By the Kamenica–Gentzkow reduction, $k_\lambda(\mu^\circ)$ is the optimal cost, so this lemma identifies the optimal posteriors in each regime.
--
--   **Formalization Note** $k_\lambda(\mu)$ is the published `BiconvexProg.BranchBound.convexEnvelope` of $\tilde K_\lambda$ over $[\omega_\ell,\omega_h]$: the supremum of $g(\mu)$ over the functions $g$ convex on $[\omega_\ell,\omega_h]$ with $g\le\tilde K_\lambda$ there. All statements assume the standing assumptions of §2 (`Params.Standing`).
-- source:
--   de Véricourt, Gurkan, Wang, Informing the Public about a Pandemic, ESMT Working Paper 20-03 (Dec. 15, 2020), p. 19 (PDF 20), Lemma 4, (36)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model
import Definitions.Def_PandemicInfo_Inequality_Reduced

namespace PandemicInfo.Inequality

/-- Lemma 4, p. 19: the lower convex envelope `k_λ` of `K̃_λ` on `[ω_ℓ, ω_h]`, regime by
regime, (36). -/
theorem lemma_4 (P : Params) (hS : P.Standing) (lam : ℝ) (μ : ℝ)
    (hμ : μ ∈ Set.Icc P.ωl P.ωh) :
    ((P.FD1 lam ∨ P.FD2 lam ∨ P.FD3 lam) →
      P.kEnv lam μ = P.Ktil lam P.ωl +
        (μ - P.ωl) / (P.ωh - P.ωl) * (P.Ktil lam P.ωh - P.Ktil lam P.ωl)) ∧
    ((P.ND1 lam ∨ P.ND2 lam) → P.kEnv lam μ = P.Ktil lam μ) ∧
    (P.DP lam →
      P.kEnv lam μ =
        if μ ≤ P.μDP lam then P.Ktil lam μ
        else P.Ktil lam (P.μDP lam) + (μ - P.μDP lam) *
          (P.Ktil lam P.ωh - P.Ktil lam (P.μDP lam)) / (P.ωh - P.μDP lam)) ∧
    (P.EX lam →
      P.kEnv lam μ =
        if P.μEX lam ≤ μ then P.Ktil lam μ
        else P.Ktil lam P.ωl + (μ - P.ωl) *
          (P.Ktil lam (P.μEX lam) - P.Ktil lam P.ωl) / (P.μEX lam - P.ωl)) := by sorry

end PandemicInfo.Inequality
