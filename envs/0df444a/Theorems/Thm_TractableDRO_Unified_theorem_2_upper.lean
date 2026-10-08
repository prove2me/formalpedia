-- Prove2me | Theorems.Thm_TractableDRO_Unified_theorem_2_upper
-- name    : TractableDRO.Unified.theorem_2_upper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:39.277526+00:00
-- url     : https://prove2.me/theorems/f672a133-1baa-49f2-8481-aec0a2cc7919
-- title:
--   Theorem 2, p. 910 (upper-bound part) — sup over 𝔽₂ of E_ℙ((r⁰ + r′ζ̃)⁺) ≤ π²(r⁰, r)
-- statement:
--   Let $F\in\mathbb R^{N\times N_E}$, $\Sigma\in\mathbb R^{N\times N}$ and $\hat{\mathcal V}\subseteq\mathbb R^{N_E}$, and let $\mathbb F_2$ be the family of probability distributions $\mathbb P$ of $\tilde\zeta\in\mathbb R^{N_E}$ with finite second moments, mean $\hat\zeta=E_{\mathbb P}(\tilde\zeta)\in\hat{\mathcal V}$ and $E_{\mathbb P}(F(\tilde\zeta-\hat\zeta)(\tilde\zeta-\hat\zeta)'F')=\Sigma$. Then for every $r^0\in\mathbb R$ and $r\in\mathbb R^{N_E}$,
--   $$\sup_{\mathbb P\in\mathbb F_2}E_{\mathbb P}\big((r^0+r'\tilde\zeta)^+\big)\le\pi^2(r^0,r)=\inf_{y:\,F'y=r}\ \sup_{\hat\zeta\in\hat{\mathcal V}}\Big\{\tfrac12(r^0+r'\hat\zeta)+\tfrac12\sqrt{(r^0+r'\hat\zeta)^2+y'\Sigma y}\Big\}.$$
--
--   This is the upper-bound half of Theorem 2 of Goh and Sim (a Scarf-type mean–variance bound); the paper also proves tightness under its standing assumptions. Theorem 4 uses only this half.
--
--   **Formalization Note** Values are extended reals; the infimum over an empty set of $y$ (when $r\notin\operatorname{range}F'$) is $+\infty$ and the left side is $-\infty$ for an empty family. No hypothesis on $F$, $\Sigma$ or $\hat{\mathcal V}$ is needed for the upper bound: membership in $\mathbb F_2$ already makes $\Sigma=F\,\mathrm{Cov}_{\mathbb P}(\tilde\zeta)F'$ positive semidefinite.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 910, Theorem 2, (22) (upper-bound part)

import Mathlib
import Definitions.Def_TractableDRO_Unified_Model

open MeasureTheory ProbabilityTheory Matrix

namespace TractableDRO.Unified

/-- Theorem 2, p. 910 (upper-bound part): `sup_{ℙ∈𝔽₂} E_ℙ((r⁰ + r′ζ̃)⁺) ≤ π²(r⁰, r)`. -/
theorem theorem_2_upper {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ)
    (Sig : Matrix (Fin N) (Fin N) ℝ) (Vhat : Set (Fin n → ℝ)) (r0 : ℝ) (r : Fin n → ℝ) :
    TractableDRO.MeanSupport.worstCase (TractableDRO.MeanCov.family2 F Sig Vhat) r0 r ≤ TractableDRO.MeanCov.pi2 F Sig Vhat r0 r := by sorry

end TractableDRO.Unified
