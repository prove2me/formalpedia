-- Prove2me | Theorems.Thm_VariationalBOED_vnmc_bound_eq_eig_of_posterior
-- name    : VariationalBOED.vnmc_bound_eq_eig_of_posterior
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T16:31:30.294489+00:00
-- url     : https://prove2.me/theorems/28a76d51-0618-4865-ae01-b9d6637e3334
-- title:
--   Lemma 1 (2): the VNMC bound is exact when the proposal is the posterior
-- statement:
--   Let $p(\theta)p(y\mid\theta,d)$ be a model and $q_v$ a valid VNMC proposal with $q_v(\theta\mid y,d)=p(\theta\mid y,d)$ for all $\theta$ and all $y$ with $p(y\mid d)>0$. Then
--
--   $$\mathcal U_{\mathrm{VNMC}}(d,L)=\mathrm{EIG}(d)\qquad\text{for all }L\ge1.$$
--
--   If the proposal is the exact posterior, every importance weight equals $p(y\mid d)$, so the VNMC bound has no bias at any $L$.
--
--   **Formalization Note** The paper requires $q_v=p(\theta\mid y,d)$ for all $y,\theta$. The posterior is defined only where $p(y\mid d)>0$, so the equality is required there. Elsewhere $q_v(\cdot\mid y,d)$ is any density, which is a $p(y\mid d)$-null case.
-- source:
--   Foster, Jankowiak, Bingham, Horsfall, Teh, Rainforth and Goodman, Variational Bayesian Optimal Experimental Design, arXiv:1903.05480v3 (NeurIPS 2019), Section 3, Lemma 1 (2), eq. (10), p. 4; proof in Appendix A.3, eq. (39), p. 14

import Mathlib
import Definitions.Def_VariationalBOED_Basic

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal

namespace VariationalBOED

theorem vnmc_bound_eq_eig_of_posterior {Th Y : Type*} [MeasurableSpace Th] [MeasurableSpace Y]
    (nuT : Measure Th) (nuY : Measure Y) [SigmaFinite nuT] [SigmaFinite nuY]
    (p : Th → ℝ) (lik : Th → Y → ℝ) (hM : IsModel nuT nuY p lik)
    (qv : Y → Th → ℝ) (hq : IsValidVNMCProposal nuT p lik qv)
    (hpost : ∀ y, 0 < marginal nuT p lik y → ∀ θ, qv y θ = posterior nuT p lik y θ) :
    ∀ L : ℕ, 1 ≤ L → vnmcBound nuT nuY p lik qv L = eig nuT nuY p lik := by sorry

end VariationalBOED
