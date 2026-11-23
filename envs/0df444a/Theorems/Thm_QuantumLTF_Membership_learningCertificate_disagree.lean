-- Prove2me | Theorems.Thm_QuantumLTF_Membership_learningCertificate_disagree
-- name    : QuantumLTF.Membership.learningCertificate_disagree
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:59:12.151378+00:00
-- url     : https://prove2.me/theorems/602ccf8a-6274-4837-a4d9-1d12cbc54d8c
-- title:
--   Endpoint/offset/gradient certificates give small disagreement
-- statement:
--   Let $n\ge2$, $0<\epsilon\le1/2$, $\|w\|=1$, and suppose that output parameters $(a,b)$ carry the analytic certificate from the endpoint/offset/gradient steps of Theorem 3.4. Then
--   \[
--   \Pr_{x\sim\gamma_n}[f_{a,b}(x)\ne f_{w,\theta}(x)]\le\epsilon.
--   \]
--
--   In the constant branch this is Lemma 3.2. In the nonconstant branch, put $\Delta=\epsilon/(100(L_\epsilon+1))$. The normalization estimates give $\|\widetilde g\|>1/4$,
--   \[
--   \|\widehat w-w\|\le8\Delta,\qquad
--   |\widehat\theta-\theta|\le\frac{4\epsilon}{100}+12L_\epsilon\Delta,
--   \]
--   and the Gaussian disagreement bound finishes the proof. The unnormalized output $a=-s\widetilde g$, $b=s\widetilde h$ represents exactly the normalized hypothesis $f_{\widehat w,\widehat\theta}$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, proof of Theorem 3.4, pp. 32–34, Eqs. (64)–(71) and final application of Lemma 2.1.

import Mathlib
import Theorems.Thm_QuantumLTF_Membership_lemma_2_1
import Theorems.Thm_QuantumLTF_Membership_lemma_3_2
import Definitions.Def_QuantumLTF_Membership_LearningCertificate

set_option maxHeartbeats 1000000

theorem QuantumLTF.Membership.learningCertificate_disagree {n : ℕ} (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) (θ : ℝ) (a : EuclideanSpace ℝ (Fin n)) (b : ℝ) (cert : QuantumLTF.Membership.LearningCertificate ε w θ a b) : QuantumLTF.Membership.disagree (QuantumLTF.Membership.ltf a b) (QuantumLTF.Membership.ltf w θ) ≤ ε := by sorry
