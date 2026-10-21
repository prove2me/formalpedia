-- Prove2me | Theorems.Thm_PandemicInfo_Inequality_lemma_3_CF
-- name    : PandemicInfo.Inequality.lemma_3_CF
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:22.979771+00:00
-- url     : https://prove2.me/theorems/07d4705e-d5d1-41d3-92b9-8d33e715d8df
-- title:
--   Lemma 3 Parts C–F, p. 18 (PDF 19) — one inflection point of $\tilde K_\lambda$; tangency at $\mu^{DP}_\lambda$, $\mu^{EX}_\lambda$
-- statement:
--   **Lemma 3, Parts C–F.** Let $\gamma=2\sigma\sqrt3$ and write $\tilde K'_\lambda$ for the derivative of $\tilde K_\lambda$.
--
--   C. If $\lambda\in(4/5,1]$ and $G_\ell(\lambda)>\kappa/\gamma\ge G_1(\lambda)$, then $\tilde K_\lambda$ is first convex and then concave, with inflection point $\mu_{in}\in(\omega_\ell,\omega_h)$, and $\tilde K'_\lambda(\omega_\ell)(\omega_h-\omega_\ell)\ge\tilde K_\lambda(\omega_h)-\tilde K_\lambda(\omega_\ell)$.
--
--   D. If $\lambda\in[0,1/2)$ and $G_2(\lambda)\ge\kappa/\gamma>G_h(\lambda)$, then $\tilde K_\lambda$ is first concave and then convex, with inflection point $\tilde\mu_{in}\in(\omega_\ell,\omega_h)$, and $\tilde K_\lambda(\omega_h)-\tilde K'_\lambda(\omega_h)(\omega_h-\omega_\ell)\ge\tilde K_\lambda(\omega_\ell)$.
--
--   E. In the regime DP ($\lambda\in(4/5,1]$, $G_1(\lambda)>\kappa/\gamma>G_h(\lambda)$), $\tilde K_\lambda$ is first convex and then concave with inflection point $\mu_{in}\in(\omega_\ell,\omega_h)$ such that $\mu^{DP}_\lambda\le\mu_{in}$, and
--   $$\tilde K_\lambda(\omega_h)-\tilde K_\lambda(\mu^{DP}_\lambda)=\tilde K'_\lambda(\mu^{DP}_\lambda)(\omega_h-\mu^{DP}_\lambda).$$
--
--   F. In the regime EX ($\lambda\in[0,1/2)$, $G_\ell(\lambda)>\kappa/\gamma>G_2(\lambda)$), $\tilde K_\lambda$ is first concave and then convex with inflection point $\tilde\mu_{in}\in(\omega_\ell,\omega_h)$ such that $\mu^{EX}_\lambda\ge\tilde\mu_{in}$, and
--   $$\tilde K_\lambda(\mu^{EX}_\lambda)-\tilde K_\lambda(\omega_\ell)=\tilde K'_\lambda(\mu^{EX}_\lambda)(\mu^{EX}_\lambda-\omega_\ell).$$
--
--   Parts E and F say that the chord from $\mu^{DP}_\lambda$ to $\omega_h$ (resp. from $\omega_\ell$ to $\mu^{EX}_\lambda$) is tangent to $\tilde K_\lambda$; this is what makes the posteriors $\{\mu^{DP}_\lambda,\omega_h\}$ (resp. $\{\omega_\ell,\mu^{EX}_\lambda\}$) optimal.
--
--   **Formalization Note** "First convex and then concave with inflection point $\mu_{in}$" is convexity on $[\omega_\ell,\mu_{in}]$ and concavity on $[\mu_{in},\omega_h]$. $\tilde K'_\lambda$ is the derivative of $\tilde K_\lambda$ within $[\omega_\ell,\omega_h]$ (`derivWithin`), one-sided at the endpoints: when $\omega_\ell\kappa=\inf\mathcal C$ the threshold $c^\star(\mu)$ leaves $\mathcal C$ for $\mu<\omega_\ell$ and $\tilde K_\lambda$ has a kink at $\omega_\ell$, so the two-sided derivative would not exist there; the paper's $\tilde K'_\lambda(\omega_\ell)$ is the derivative of the formula (39), i.e. the one-sided one. The proofs of Parts C and D in the paper reverse "convex" and "concave"; the statements, formalized here, are the correct ones. All statements assume the standing assumptions of §2 (`Params.Standing`).
-- source:
--   de Véricourt, Gurkan, Wang, Informing the Public about a Pandemic, ESMT Working Paper 20-03 (Dec. 15, 2020), p. 18 (PDF 19), Lemma 3 Parts C–F

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model
import Definitions.Def_PandemicInfo_Inequality_Reduced

namespace PandemicInfo.Inequality

/-- Lemma 3 Parts C–F, p. 18: in the intermediate regimes `K̃_λ` changes curvature once inside
`(ω_ℓ, ω_h)`; the chord/tangent inequalities of C and D and the tangency equations of E and F.
`K̃'_λ` is the derivative of `K̃_λ` within `[ω_ℓ, ω_h]` (one-sided at the endpoints). -/
theorem lemma_3_CF (P : Params) (hS : P.Standing) (lam : ℝ) :
    -- Part C
    ((lam ∈ Set.Ioc (4 / 5 : ℝ) 1 ∧ P.κ / P.γ < P.Gl lam ∧ P.G1 lam ≤ P.κ / P.γ) →
      ∃ μin ∈ Set.Ioo P.ωl P.ωh,
        ConvexOn ℝ (Set.Icc P.ωl μin) (P.Ktil lam) ∧
        ConcaveOn ℝ (Set.Icc μin P.ωh) (P.Ktil lam) ∧
        P.Ktil lam P.ωh - P.Ktil lam P.ωl ≤
          derivWithin (P.Ktil lam) (Set.Icc P.ωl P.ωh) P.ωl * (P.ωh - P.ωl)) ∧
    -- Part D
    ((lam ∈ Set.Ico (0 : ℝ) (1 / 2) ∧ P.κ / P.γ ≤ P.G2 lam ∧ P.Gh lam < P.κ / P.γ) →
      ∃ μin ∈ Set.Ioo P.ωl P.ωh,
        ConcaveOn ℝ (Set.Icc P.ωl μin) (P.Ktil lam) ∧
        ConvexOn ℝ (Set.Icc μin P.ωh) (P.Ktil lam) ∧
        P.Ktil lam P.ωl ≤ P.Ktil lam P.ωh -
          derivWithin (P.Ktil lam) (Set.Icc P.ωl P.ωh) P.ωh * (P.ωh - P.ωl)) ∧
    -- Part E
    (P.DP lam →
      ∃ μin ∈ Set.Ioo P.ωl P.ωh,
        ConvexOn ℝ (Set.Icc P.ωl μin) (P.Ktil lam) ∧
        ConcaveOn ℝ (Set.Icc μin P.ωh) (P.Ktil lam) ∧
        P.μDP lam ≤ μin ∧
        P.Ktil lam P.ωh - P.Ktil lam (P.μDP lam) =
          derivWithin (P.Ktil lam) (Set.Icc P.ωl P.ωh) (P.μDP lam) * (P.ωh - P.μDP lam)) ∧
    -- Part F
    (P.EX lam →
      ∃ μin ∈ Set.Ioo P.ωl P.ωh,
        ConcaveOn ℝ (Set.Icc P.ωl μin) (P.Ktil lam) ∧
        ConvexOn ℝ (Set.Icc μin P.ωh) (P.Ktil lam) ∧
        μin ≤ P.μEX lam ∧
        P.Ktil lam (P.μEX lam) - P.Ktil lam P.ωl =
          derivWithin (P.Ktil lam) (Set.Icc P.ωl P.ωh) (P.μEX lam) * (P.μEX lam - P.ωl)) := by sorry

end PandemicInfo.Inequality
