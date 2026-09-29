-- Prove2me | Theorems.Thm_TreatmentLocality_fderiv_mbATE_apply
-- name    : TreatmentLocality.fderiv_mbATE_apply
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T00:40:30.412433+00:00
-- url     : https://prove2.me/theorems/77e61109-436c-435f-a745-196eb29b1b4b
-- title:
--   Gradient of the model-based ATE estimator
-- statement:
--   **The gradient of the model-based ATE estimator.** At a statistics vector $v$ where every visit count $N^a_i = \sum_k K^a_{ik}$ is nonzero and both plug-in Bellman system matrices $B^a = \mathrm{Diag}(N^a) - \gamma K^a$ are invertible, the estimator $\hat\Delta_s = \hat V^t_s - \hat V^c_s$ is Fréchet differentiable, with derivative in the direction $h = (\mathrm{d}K, \mathrm{d}R)$ given arm by arm:
--   $$\mathrm{d}\hat\Delta_s[h] \;=\; \bigl((B^t)^{-1} w^t\bigr)_s - \bigl((B^c)^{-1} w^c\bigr)_s,\qquad w^a_i \;=\; \mathrm{d}R^a_i + \sum_j \mathrm{d}K^a_{ij}\,\bigl(\gamma \hat V^a_j - \hat V^a_i\bigr).$$
--
--   The perturbation of the transition counts of arm $a$ enters only through the temporal-difference residual $\gamma\hat V^a_j - \hat V^a_i$ — the contributions from renormalising the rows cancel against the plug-in Bellman equation. This is the linearisation at which the delta method evaluates the estimator (arXiv:2407.19618, Lemma EC.5 and Theorems 3-4); its asymptotic covariance under the experiment chain is the matrix $\Sigma_{IS}$ appearing in the efficiency bound of Theorem 5, and the fact that the residual is centred given the current state is what makes that linearisation a martingale difference.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, Section 2, Remark 1 and Proposition 5 (the plug-in estimator), Definition 1 and Lemma EC.5 (differentiable estimators and their linearisation), and Appendix EC.4.3, where the same derivatives ∂Δ/∂P(s,j) = γ(I-γP)⁻¹E_{s,j}V and ∂Δ/∂r are computed.

import Definitions.Def_TreatmentLocalityPlugIn

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.fderiv_mbATE_apply {S : Type*} [DecidableEq S] [Fintype S]
    (M : Model S) (v : EstInput S)
    (hN : ∀ a i, ∑ k, (v a).1 i k ≠ 0) (hB : ∀ a, IsUnit (mbSystem M v a))
    (s : S) (h : EstInput S) :
    fderiv ℝ (fun u : EstInput S => mbATE M u s) v h
      = ((mbSystem M v true)⁻¹.mulVec (fun i =>
          (h true).2 i + ∑ j, (h true).1 i j *
            (M.γdisc * mbValue M v true j - mbValue M v true i))) s
        - ((mbSystem M v false)⁻¹.mulVec (fun i =>
          (h false).2 i + ∑ j, (h false).1 i j *
            (M.γdisc * mbValue M v false j - mbValue M v false i))) s := by sorry
