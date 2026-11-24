-- Prove2me | Theorems.Thm_VariationalBOED_ml_error_bound
-- name    : VariationalBOED.ml_error_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T17:15:19.99291+00:00
-- url     : https://prove2.me/theorems/3436fad3-7959-4bc0-9b7a-4960eda68bdd
-- title:
--   Lemma 2: error bound for the marginal + likelihood estimate
-- statement:
--   Let $p(\theta)p(y\mid\theta,d)$ be a model. Let $q_m(y\mid d)$ be a probability density with the same support as $p(y\mid d)$, and $q_\ell(y\mid\theta,d)$ a conditional density with the same support as $p(y\mid\theta,d)$. Suppose the expectations $\mathbb E_{p(y,\theta\mid d)}[\log p(y\mid\theta,d)]$, $\mathbb E_{p(y,\theta\mid d)}[\log p(y\mid d)]$, $\mathbb E_{p(y,\theta\mid d)}[\log q_m(y\mid d)]$ and $\mathbb E_{p(y,\theta\mid d)}[\log q_\ell(y\mid\theta,d)]$ are finite. Then
--
--   $$\big|\mathcal I_{m+\ell}(d)-\mathrm{EIG}(d)\big|\le-\mathbb E_{p(y,\theta\mid d)}\big[\log q_m(y\mid d)+\log q_\ell(y\mid\theta,d)\big]+C,$$
--
--   where $C=-H[p(y\mid d)]-\mathbb E_{p(\theta)}\big[H(p(y\mid\theta,d))\big]$ does not depend on $q_m$ or $q_\ell$. Further, the right-hand side is $0$ if and only if $q_m(y\mid d)=p(y\mid d)$ for $\nu_{\mathcal Y}$-almost all $y$ and $q_\ell(y\mid\theta,d)=p(y\mid\theta,d)$ for almost all $(\theta,y)$ with respect to $p(\theta)\,d\nu_\Theta\otimes\nu_{\mathcal Y}$.
--
--   This justifies training $q_m$ and $q_\ell$ by maximizing $\mathbb E[\log q_m(y\mid d)+\log q_\ell(y\mid\theta,d)]$ for implicit-likelihood models.
--
--   **Formalization Note** The finiteness hypotheses make $C$ and every expectation in (13) a real number, as the paper's statement presupposes. The paper's "for almost all $y,\theta$" is read with respect to $p(y\mid d)$ (equivalently $\nu_{\mathcal Y}$, by the support condition) for $q_m$ and with respect to $p(\theta)\,d\nu_\Theta\otimes\nu_{\mathcal Y}$ for $q_\ell$.
-- source:
--   Foster, Jankowiak, Bingham, Horsfall, Teh, Rainforth and Goodman, Variational Bayesian Optimal Experimental Design, arXiv:1903.05480v3 (NeurIPS 2019), Section 3, Lemma 2, eqs. (12)-(13), p. 5; proof in Appendix A.4, eqs. (45)-(56), p. 15

import Mathlib
import Definitions.Def_VariationalBOED_Basic

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal

namespace VariationalBOED

theorem ml_error_bound {Th Y : Type*} [MeasurableSpace Th] [MeasurableSpace Y]
    (nuT : Measure Th) (nuY : Measure Y) [SigmaFinite nuT] [SigmaFinite nuY]
    (p : Th → ℝ) (lik : Th → Y → ℝ) (hM : IsModel nuT nuY p lik)
    (qm : Y → ℝ) (hqm : IsValidMarginalApprox nuT nuY p lik qm)
    (ql : Th → Y → ℝ) (hql : IsValidLikelihoodApprox nuY lik ql)
    (hlik : Integrable (fun z : Th × Y => Real.log (lik z.1 z.2)) (jointLaw nuT nuY p lik))
    (hmarg : Integrable (fun z : Th × Y => Real.log (marginal nuT p lik z.2))
      (jointLaw nuT nuY p lik))
    (hqmi : Integrable (fun z : Th × Y => Real.log (qm z.2)) (jointLaw nuT nuY p lik))
    (hqli : Integrable (fun z : Th × Y => Real.log (ql z.1 z.2)) (jointLaw nuT nuY p lik)) :
    |mlEstimate nuT nuY p lik qm ql - eig nuT nuY p lik| ≤
      -(∫ z, (Real.log (qm z.2) + Real.log (ql z.1 z.2)) ∂jointLaw nuT nuY p lik) +
        (-diffEntropy nuY (marginal nuT p lik) -
          ∫ θ, diffEntropy nuY (lik θ) ∂densMeasure nuT p) ∧
    (-(∫ z, (Real.log (qm z.2) + Real.log (ql z.1 z.2)) ∂jointLaw nuT nuY p lik) +
        (-diffEntropy nuY (marginal nuT p lik) -
          ∫ θ, diffEntropy nuY (lik θ) ∂densMeasure nuT p) = 0 ↔
      qm =ᵐ[nuY] marginal nuT p lik ∧
        ∀ᵐ z ∂(densMeasure nuT p).prod nuY, ql z.1 z.2 = lik z.1 z.2) := by sorry

end VariationalBOED
