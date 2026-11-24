-- Prove2me | Theorems.Thm_VariationalBOED_ml_estimate_le_eig_of_coupled
-- name    : VariationalBOED.ml_estimate_le_eig_of_coupled
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T17:27:32.858894+00:00
-- url     : https://prove2.me/theorems/2ca67f4c-0d2c-497e-bf94-50cf0980ec9b
-- title:
--   Appendix A.4: with $q_m = E_{p(\theta)}[q_\ell]$ the marginal + likelihood estimate is a lower bound
-- statement:
--   Let $p(\theta)p(y\mid\theta,d)$ be a model and $q_\ell(y\mid\theta,d)$ a conditional density with the same support as $p(y\mid\theta,d)$. Couple the marginal approximation to it by
--
--   $$q_m(y\mid d)=\mathbb E_{p(\theta)}\big[q_\ell(y\mid\theta,d)\big].$$
--
--   If $\mathrm{EIG}(d)$ and $\mathcal I_{m+\ell}(d)$ are finite, then
--
--   $$\mathcal I_{m+\ell}(d)\le\mathrm{EIG}(d).$$
--
--   With this coupling the marginal + likelihood estimate becomes a lower bound, whereas for separately learned $q_m,q_\ell$ it is neither an upper nor a lower bound.
--
--   **Formalization Note** Finiteness of $\mathrm{EIG}(d)$ and of $\mathcal I_{m+\ell}(d)$ is assumed explicitly.
-- source:
--   Foster, Jankowiak, Bingham, Horsfall, Teh, Rainforth and Goodman, Variational Bayesian Optimal Experimental Design, arXiv:1903.05480v3 (NeurIPS 2019), Appendix A.4, final observation, eqs. (57)-(62), pp. 15-16

import Mathlib
import Definitions.Def_VariationalBOED_Basic

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal

namespace VariationalBOED

theorem ml_estimate_le_eig_of_coupled {Th Y : Type*} [MeasurableSpace Th] [MeasurableSpace Y]
    (nuT : Measure Th) (nuY : Measure Y) [SigmaFinite nuT] [SigmaFinite nuY]
    (p : Th → ℝ) (lik : Th → Y → ℝ) (hM : IsModel nuT nuY p lik)
    (ql : Th → Y → ℝ) (hql : IsValidLikelihoodApprox nuY lik ql)
    (hEIG : Integrable (eigIntegrand nuT p lik) (jointLaw nuT nuY p lik))
    (hI : Integrable (mlIntegrand (marginal nuT p ql) ql) (jointLaw nuT nuY p lik)) :
    mlEstimate nuT nuY p lik (marginal nuT p ql) ql ≤ eig nuT nuY p lik := by sorry

end VariationalBOED
