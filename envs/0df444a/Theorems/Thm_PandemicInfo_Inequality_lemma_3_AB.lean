-- Prove2me | Theorems.Thm_PandemicInfo_Inequality_lemma_3_AB
-- name    : PandemicInfo.Inequality.lemma_3_AB
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:06.26302+00:00
-- url     : https://prove2.me/theorems/d28db567-3ebf-4239-bdd8-c1f58f9bcaa3
-- title:
--   Lemma 3 Parts A–B, p. 18 (PDF 19) — $\tilde K_\lambda$ concave or convex on $[\omega_\ell,\omega_h]$
-- statement:
--   **Lemma 3, Parts A and B.** Let $\gamma=2\sigma\sqrt3$.
--
--   A. $\tilde K_\lambda$ is concave on $[\omega_\ell,\omega_h]$ if either one of the following conditions holds:
--      1. $\lambda\in[1/2,4/5]$;
--      2. $\lambda\in(4/5,1]$ and $\kappa/\gamma\ge G_\ell(\lambda)$;
--      3. $\lambda\in[0,1/2)$ and $G_h(\lambda)\ge\kappa/\gamma$.
--
--   B. $\tilde K_\lambda$ is convex on $[\omega_\ell,\omega_h]$ if either one of the following conditions holds:
--      1. $\lambda\in[0,1/2)$ and $\kappa/\gamma\ge G_\ell(\lambda)$;
--      2. $\lambda\in(4/5,1]$ and $G_h(\lambda)\ge\kappa/\gamma$.
--
--   Concavity of $\tilde K_\lambda$ makes full disclosure optimal and convexity makes no disclosure optimal (Lemma 4, Theorem 1).
--
--   **Formalization Note** All statements assume the standing assumptions of §2, bundled in `Params.Standing`: $0<\omega_\ell<\omega_h<1$, $0<\rho^\circ<1$, $\theta\ge\sigma\sqrt3>0$, $\kappa>0$ and $\omega_\ell\kappa\ge\inf\mathcal C$.
-- source:
--   de Véricourt, Gurkan, Wang, Informing the Public about a Pandemic, ESMT Working Paper 20-03 (Dec. 15, 2020), p. 18 (PDF 19), Lemma 3 Parts A–B

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model
import Definitions.Def_PandemicInfo_Inequality_Reduced

namespace PandemicInfo.Inequality

/-- Lemma 3 Parts A and B, p. 18: concavity and convexity of `K̃_λ` on `[ω_ℓ, ω_h]`. -/
theorem lemma_3_AB (P : Params) (hS : P.Standing) (lam : ℝ) :
    ((lam ∈ Set.Icc (1 / 2 : ℝ) (4 / 5) ∨
        (lam ∈ Set.Ioc (4 / 5 : ℝ) 1 ∧ P.Gl lam ≤ P.κ / P.γ) ∨
        (lam ∈ Set.Ico (0 : ℝ) (1 / 2) ∧ P.κ / P.γ ≤ P.Gh lam)) →
      ConcaveOn ℝ (Set.Icc P.ωl P.ωh) (P.Ktil lam)) ∧
    (((lam ∈ Set.Ico (0 : ℝ) (1 / 2) ∧ P.Gl lam ≤ P.κ / P.γ) ∨
        (lam ∈ Set.Ioc (4 / 5 : ℝ) 1 ∧ P.κ / P.γ ≤ P.Gh lam)) →
      ConvexOn ℝ (Set.Icc P.ωl P.ωh) (P.Ktil lam)) := by sorry

end PandemicInfo.Inequality
