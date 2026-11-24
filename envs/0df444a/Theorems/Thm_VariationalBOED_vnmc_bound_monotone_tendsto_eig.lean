-- Prove2me | Theorems.Thm_VariationalBOED_vnmc_bound_monotone_tendsto_eig
-- name    : VariationalBOED.vnmc_bound_monotone_tendsto_eig
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T17:00:02.756264+00:00
-- url     : https://prove2.me/theorems/9dd86435-f434-4075-b83e-91c11cc51f94
-- title:
--   Lemma 1 (1) (as proved): the VNMC bound decreases in $L$ to the EIG
-- statement:
--   Let $p(\theta)p(y\mid\theta,d)$ be a model and let $q_v(\theta\mid y,d)$ be a valid VNMC proposal. Valid means that $q_v$ is a conditional density with the same support as the posterior and that, for every $y$ with $p(y\mid d)>0$, the weight $p(y,\theta\mid d)/q_v(\theta\mid y,d)$ is bounded in $\theta$. Suppose $\mathrm{EIG}(d)$ and $\mathcal U_{\mathrm{VNMC}}(d,1)$ are finite. Then
--
--   $$\mathrm{EIG}(d)=\lim_{L\to\infty}\mathcal U_{\mathrm{VNMC}}(d,L)\le\mathcal U_{\mathrm{VNMC}}(d,L_2)\le\mathcal U_{\mathrm{VNMC}}(d,L_1)\qquad\text{for all }L_2\ge L_1\ge1.$$
--
--   The VNMC bound is therefore an upper bound on the EIG that can be made arbitrarily tight by increasing $L$, even when the variational family does not contain the posterior. This is the property that makes $\hat\mu_{\mathrm{VNMC}}$ consistent.
--
--   **Formalization Note** The hypothesis that $\mathcal U_{\mathrm{VNMC}}(d,1)$ is finite does not appear in the printed lemma. The monotone-limit step of the proof in Appendix A.3 needs it, and without it the limit claim fails: there are valid proposals with $\mathrm{EIG}(d)=0$ and $\mathcal U_{\mathrm{VNMC}}(d,L)=+\infty$ for every $L$. Finiteness of $\mathrm{EIG}(d)$ is assumed because the quantities are real numbers in Lean.
-- source:
--   Foster, Jankowiak, Bingham, Horsfall, Teh, Rainforth and Goodman, Variational Bayesian Optimal Experimental Design, arXiv:1903.05480v3 (NeurIPS 2019), Section 3, Lemma 1 (1), eq. (10), p. 4; proof in Appendix A.3, eqs. (28)-(38), pp. 13-14

import Mathlib
import Definitions.Def_VariationalBOED_Basic

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal

namespace VariationalBOED

theorem vnmc_bound_monotone_tendsto_eig {Th Y : Type*} [MeasurableSpace Th] [MeasurableSpace Y]
    (nuT : Measure Th) (nuY : Measure Y) [SigmaFinite nuT] [SigmaFinite nuY]
    (p : Th → ℝ) (lik : Th → Y → ℝ) (hM : IsModel nuT nuY p lik)
    (qv : Y → Th → ℝ) (hq : IsValidVNMCProposal nuT p lik qv)
    (hEIG : Integrable (eigIntegrand nuT p lik) (jointLaw nuT nuY p lik))
    (hU1 : Integrable (vnmcIntegrand p lik qv 1) (vnmcLaw nuT nuY p lik qv 1)) :
    Tendsto (fun L : ℕ => vnmcBound nuT nuY p lik qv L) atTop (𝓝 (eig nuT nuY p lik)) ∧
    (∀ L : ℕ, 1 ≤ L → eig nuT nuY p lik ≤ vnmcBound nuT nuY p lik qv L) ∧
    (∀ L₁ L₂ : ℕ, 1 ≤ L₁ → L₁ ≤ L₂ →
      vnmcBound nuT nuY p lik qv L₂ ≤ vnmcBound nuT nuY p lik qv L₁) := by sorry

end VariationalBOED
