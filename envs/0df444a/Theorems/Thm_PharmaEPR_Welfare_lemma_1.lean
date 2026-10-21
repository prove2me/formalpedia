-- Prove2me | Theorems.Thm_PharmaEPR_Welfare_lemma_1
-- name    : PharmaEPR.Welfare.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:18.81935+00:00
-- url     : https://prove2.me/theorems/9b3bf314-bdfb-4f47-946d-a5adbc92265b
-- title:
--   Lemma 1, p. 15 — the doctor's optimal prescription and participation condition
-- statement:
--   Let the doctor's reputational cost satisfy $o_d\ge0$, let patient-directed promotion be in $[0,1]$, and let need $\theta_n\in[0,1]$. Given price and promotion, the model's prescription $q_p$ lies in $[\theta_n,1]$ and maximizes the doctor's utility there:
--
--   $$U_d(q)\le U_d(q_p)\qquad(\theta_n\le q\le1).$$
--
--   If $\eta_d<p+o_d(1-\eta_p)$ and $\theta_n<1$, $q_p=\theta_n$ is the unique maximizer. If $\eta_d>p+o_d(1-\eta_p)$ and $\theta_n<1$, $q_p=1$ is the unique maximizer. For $\theta_n>0$, nonnegative utility at the need prescription is equivalent to $p-u_p\le\eta_d$.
--
--   This result validates the doctor's response used throughout the producer and planner problems. At equality in the incentive comparison the doctor is indifferent; the model chooses $q_p=1$.
-- source:
--   Alev, Atasu, Toktay & Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020-09-05 posting), p. 15, Lemma 1; proof Online Appendix p. 1

import Mathlib
import Definitions.Def_PharmaEPR_Welfare_Model

namespace PharmaEPR.Welfare

theorem lemma_1 (P : Params) (a : Action) (thetaN : ℝ)
    (hod : 0 ≤ P.od) (hetaP0 : 0 ≤ a.etaP) (hetaP1 : a.etaP ≤ 1)
    (hneed : thetaN ∈ Set.Icc (0 : ℝ) 1) :
    presc P a thetaN ∈ Set.Icc thetaN 1 ∧
    (∀ q ∈ Set.Icc thetaN 1,
      docUtil P a thetaN q ≤ docUtil P a thetaN (presc P a thetaN)) ∧
    (a.etaD < a.p + P.od * (1 - a.etaP) → thetaN < 1 →
      ∀ q ∈ Set.Icc thetaN 1,
        docUtil P a thetaN q = docUtil P a thetaN thetaN → q = thetaN) ∧
    (a.p + P.od * (1 - a.etaP) < a.etaD → thetaN < 1 →
      ∀ q ∈ Set.Icc thetaN 1,
        docUtil P a thetaN q = docUtil P a thetaN 1 → q = 1) ∧
    (0 < thetaN →
      (0 ≤ docUtil P a thetaN thetaN ↔ a.p - P.up ≤ a.etaD)) := by sorry

end PharmaEPR.Welfare
