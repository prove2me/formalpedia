-- Prove2me | Theorems.Thm_TractableDRO_Unified_theorem_3
-- name    : TractableDRO.Unified.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:50.892916+00:00
-- url     : https://prove2.me/theorems/ab4d96b9-0602-42a2-bd0d-66dce8774fa3
-- title:
--   Theorem 3, p. 910 — sup over 𝔽₃ of E_ℙ((r⁰ + r′ζ̃)⁺) ≤ π³(r⁰, r) under directional-deviation bounds
-- statement:
--   Let $F_\sigma\in\mathbb R^{N_\sigma\times N_E}$, $g_\sigma\in\mathbb R^{N_\sigma}$, $\hat{\mathcal V}\subseteq\mathbb R^{N_E}$, $\hat{\mathcal W}_\sigma\subseteq\mathbb R^{N_\sigma}$, and deviation bounds $\sigma_f,\sigma_b\in\mathbb R^{N_\sigma}$ with $\sigma_f\ge0$, $\sigma_b\ge0$. Assume
--   $$F_\sigma\hat\zeta+g_\sigma\in\hat{\mathcal W}_\sigma\quad\text{for every }\hat\zeta\in\hat{\mathcal V}.$$
--   Let $\mathbb F_3$ be the family of probability distributions $\mathbb P$ of $\tilde\zeta\in\mathbb R^{N_E}$ with finite mean $\hat\zeta\in\hat{\mathcal V}$ such that $\tilde z_\sigma=F_\sigma\tilde\zeta+g_\sigma$ has independent components, each with finite exponential moments and with forward and backward deviations at most $\sigma_{f,j}$ and $\sigma_{b,j}$. Then for every $r^0\in\mathbb R$ and $r\in\mathbb R^{N_E}$,
--   $$\sup_{\mathbb P\in\mathbb F_3}E_{\mathbb P}\big((r^0+r'\tilde\zeta)^+\big)\le\pi^3(r^0,r),$$
--   where
--   $$\pi^3(r^0,r)=\inf_{\substack{s^0,s,x^0,x:\\ x^0+x'g_\sigma=r^0,\ F_\sigma'x=r}}\Big\{(r^0-s^0-s'g_\sigma)+\sup_{\hat\zeta\in\hat{\mathcal V}}(r'-s'F_\sigma)\hat\zeta+\psi(s^0-x^0,s-x)+\psi(s^0,s)\Big\},$$
--   $$\psi(x^0,x)=\inf_{\lambda>0}\Big\{\frac{\lambda}{e}\exp\Big(\frac1\lambda\sup_{\hat z_\sigma\in\hat{\mathcal W}_\sigma}\{x^0+x'\hat z_\sigma\}+\frac{\|u\|_2^2}{2\lambda^2}\Big)\Big\},\qquad u_j=\max\{x_j\sigma_{f,j},-x_j\sigma_{b,j}\}.$$
--
--   This is Theorem 3 of Goh and Sim. Unlike $\pi^1$ and $\pi^2$, the bound $\pi^3$ is not tight, but it exploits componentwise independence; it is the third ingredient of the unified bound of Theorem 4.
--
--   **Formalization Note** The two added hypotheses come from the paper's model: deviations are square roots, so the bounds $\sigma_f\ge\sigma_{f\mathbb P}$, $\sigma_b\ge\sigma_{b\mathbb P}$ of p. 905 are nonnegative, and the inclusion follows from $\hat{\mathcal W}_\sigma=\{H_\sigma\hat z:\hat z\in\hat{\mathcal W}\}$ (p. 905), $\hat{\mathcal V}=\{\hat\zeta: F\hat\zeta+g\in\hat{\mathcal W}\}$ (p. 908) and $F_\sigma=H_\sigma F$, $g_\sigma=H_\sigma g$ (Remark after Theorem 3, p. 910). The deviation bounds are the published `FwdDevLe`/`BwdDevLe` predicates applied to the law of $\tilde z_{\sigma,j}$. Values are in `EReal`; in $\psi$ the supremum over $\hat{\mathcal W}_\sigma$ is taken outside the increasing exponential, which is the same function when $\hat{\mathcal W}_\sigma\neq\emptyset$ (guaranteed by the inclusion when $\hat{\mathcal V}\ne\emptyset$; when $\hat{\mathcal V}=\emptyset$ the family is empty).
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 910, Theorem 3, (24); p. 905 (Directional Deviations); p. 908 (𝒱̂); p. 910 (Remark after Theorem 3)

import Mathlib
import Definitions.Def_TractableDRO_Unified_Model

open MeasureTheory ProbabilityTheory Matrix

namespace TractableDRO.Unified

/-- Theorem 3, p. 910: `sup_{ℙ∈𝔽₃} E_ℙ((r⁰ + r′ζ̃)⁺) ≤ π³(r⁰, r)`, for nonnegative deviation
bounds and `𝒲̂_σ ⊇ {F_σ ζ̂ + g_σ : ζ̂ ∈ 𝒱̂}` (from `𝒲̂_σ = H_σ 𝒲̂`, `𝒱̂ = {ζ̂ : Fζ̂ + g ∈ 𝒲̂}`,
`F_σ = H_σ F`, `g_σ = H_σ g`, pp. 905, 908, 910). -/
theorem theorem_3 {n Nσ : ℕ} (Fσ : Matrix (Fin Nσ) (Fin n) ℝ) (gσ : Fin Nσ → ℝ)
    (Vhat : Set (Fin n → ℝ)) (Wσhat : Set (Fin Nσ → ℝ)) (σf σb : Fin Nσ → ℝ)
    (hσf : 0 ≤ σf) (hσb : 0 ≤ σb) (hW : ∀ ζh ∈ Vhat, Fσ *ᵥ ζh + gσ ∈ Wσhat)
    (r0 : ℝ) (r : Fin n → ℝ) :
    TractableDRO.MeanSupport.worstCase (family3 Fσ gσ Vhat σf σb) r0 r ≤ pi3 Fσ gσ Vhat Wσhat σf σb r0 r := by sorry

end TractableDRO.Unified
