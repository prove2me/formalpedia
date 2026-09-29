-- Prove2me | Theorems.Thm_TreatmentLocality_fderiv_mbATE_estObs
-- name    : TreatmentLocality.fderiv_mbATE_estObs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:54:26.702485+00:00
-- url     : https://prove2.me/theorems/6f981d4f-cbca-4c0a-b14b-117cbc5decd8
-- title:
--   The influence function of the model-based estimator is a weighted temporal-difference error
-- statement:
--   **The influence function of the model-based estimator, in closed form.** Differentiate the model-based plug-in estimator $\hat\Delta = \hat V^t - \hat V^c$ at a statistic vector $v$ with positive visit counts and invertible plug-in Bellman system, and evaluate the derivative on the per-step statistic $u_{\mathrm{IS}}(X)$ of a *single* information-sharing observation $X = (s, \gamma, s', r)$. The whole expression collapses to a difference of two inverse-probability-weighted temporal-difference errors,
--   $$\nabla\hat\Delta(v)\bigl[u_{\mathrm{IS}}(X)\bigr](s_0) \;=\; \sum_{a \in \{t,c\}} \pm\, B_a^{-1}(s_0, s)\, w_a(X)\,\bigl(r + \gamma \hat V^a(s') - \hat V^a(s)\bigr),$$
--   where $B_a = \mathrm{Diag}(N^a) - \gamma K^a$ is the plug-in Bellman system and $w_a$ is the information-sharing weight.
--
--   Two things collapse at once. The reward statistic $R^a_{\mathrm{IS}}$ is supported on the event $\{s_i = s\}$, so only the row of the current state survives; and the transition statistic $K^a_{\mathrm{IS}}$ enters *only* through the temporal-difference residual, because the terms coming from renormalising the row cancel against the plug-in Bellman equation. So a single observation contributes one weighted TD error at the state it visits, and nothing else — which is what makes the asymptotic analysis of the estimator a martingale argument rather than a delta-method bookkeeping exercise (arXiv:2407.19618, Remark 1, Proposition 5, Appendix EC.3.2).
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3: Remark 1 and Proposition 5 (the model-based plug-in estimator), §6.2 (the information-sharing statistics), and Appendix EC.3.2 (the linearisation of a differentiable estimator and its asymptotic covariance, Lemma EC.4-EC.5).

import Definitions.Def_TreatmentLocalityPlugIn
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.fderiv_mbATE_estObs {S : Type*} [DecidableEq S] [Fintype S]
    (M : Model S) (v : EstInput S)
    (hN : ∀ a i, ∑ k, (v a).1 i k ≠ 0) (hB : ∀ a, IsUnit (mbSystem M v a))
    (s : S) (z : Step S) :
    fderiv ℝ (fun u : EstInput S => mbATE M u s) v (estObs M .IS z)
      = (mbSystem M v true)⁻¹ s (Step.state z) *
          (schemeWeight M .IS true z *
            (Step.rwd z + M.γdisc * mbValue M v true (Step.next z)
              - mbValue M v true (Step.state z)))
        - (mbSystem M v false)⁻¹ s (Step.state z) *
          (schemeWeight M .IS false z *
            (Step.rwd z + M.γdisc * mbValue M v false (Step.next z)
              - mbValue M v false (Step.state z))) := by sorry
