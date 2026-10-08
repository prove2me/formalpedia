-- Prove2me | Theorems.Thm_TractableDRO_Unified_theorem_1_upper
-- name    : TractableDRO.Unified.theorem_1_upper
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:40.356865+00:00
-- url     : https://prove2.me/theorems/ad7713e9-457e-4764-93d3-e91afd4f3480
-- title:
--   Theorem 1, p. 909 (upper-bound part) — sup over 𝔽₁ of E_ℙ((r⁰ + r′ζ̃)⁺) ≤ π¹(r⁰, r)
-- statement:
--   Let $\mathcal V,\hat{\mathcal V}\subseteq\mathbb R^{N_E}$ be arbitrary sets and let $\mathbb F_1$ be the family of probability distributions $\mathbb P$ of a random vector $\tilde\zeta\in\mathbb R^{N_E}$ with finite mean $\hat\zeta=E_{\mathbb P}(\tilde\zeta)\in\hat{\mathcal V}$ and $\mathbb P(\tilde\zeta\in\mathcal V)=1$. Then for every $r^0\in\mathbb R$ and $r\in\mathbb R^{N_E}$,
--   $$\sup_{\mathbb P\in\mathbb F_1}E_{\mathbb P}\big((r^0+r'\tilde\zeta)^+\big)\le\pi^1(r^0,r)=\inf_{s\in\mathbb R^{N_E}}\Big(\sup_{\hat\zeta\in\hat{\mathcal V}}s'\hat\zeta+\sup_{\zeta\in\mathcal V}\max\{r^0+r'\zeta-s'\zeta,\,-s'\zeta\}\Big).$$
--
--   This is the upper-bound half of Theorem 1 of Goh and Sim; the paper also proves that the bound is tight under its standing assumptions. Theorem 4 uses only this half.
--
--   **Formalization Note** Both sides are extended reals: the left side is $-\infty$ when $\mathbb F_1$ is empty, and infinite suprema are allowed on the right. No convexity or closedness of $\mathcal V,\hat{\mathcal V}$ is assumed; the upper bound does not need it.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 909, Theorem 1, (21) (upper-bound part)

import Mathlib
import Definitions.Def_TractableDRO_Unified_Model

open MeasureTheory ProbabilityTheory Matrix

namespace TractableDRO.Unified

/-- Theorem 1, p. 909 (upper-bound part): `sup_{ℙ∈𝔽₁} E_ℙ((r⁰ + r′ζ̃)⁺) ≤ π¹(r⁰, r)`. -/
theorem theorem_1_upper {n : ℕ} (V Vhat : Set (Fin n → ℝ)) (r0 : ℝ) (r : Fin n → ℝ) :
    TractableDRO.MeanSupport.worstCase (TractableDRO.MeanSupport.family1 V Vhat) r0 r ≤ pi1 V Vhat r0 r := by sorry

end TractableDRO.Unified
