-- Prove2me | Theorems.Thm_PrivacyQueue_Control_lemma_4
-- name    : PrivacyQueue.Control.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:17.240665+00:00
-- url     : https://prove2.me/theorems/ece2ef62-62db-4de3-9b6d-0a2853063fd8
-- title:
--   Lemma 4 — total customer surplus increases under SPT and decreases under LPT
-- statement:
--   Let $CS(\gamma)$ be total customer surplus when a fraction $\gamma\in[0,1]$ of customers discloses request type. Under shortest-processing-time priority ($\sigma<1$), surplus is nondecreasing in $\gamma$; under longest-processing-time priority ($\sigma>1$), it is nonincreasing:
--
--   $$\sigma<1\implies CS\text{ is nondecreasing on }[0,1],\qquad \sigma>1\implies CS\text{ is nonincreasing on }[0,1].$$
--
--   If both request types occur with positive probability, $0<\alpha<1$, the respective monotonicity is strict. This is the source lemma used to compare an equilibrium under customer control with full disclosure.
--
--   **Formalization Note** The source's word “increases” is separated into weak monotonicity for $\alpha\in[0,1]$ and strict monotonicity for $0<\alpha<1$. When $\alpha=0$ or $\alpha=1$, $CS$ is constant. No critical-value exclusion is imposed on this lemma.
-- source:
--   Hu, Momot & Wang, Privacy Management in Service Systems, submitted manuscript (draft of 12 Feb 2022; SSRN 3628751), Online Appendix p. 3 (PDF 37), Lemma 4; proof in Online Supplement p. 2 (PDF 49)

import Mathlib
import Definitions.Def_PrivacyQueue_Control_Model

namespace PrivacyQueue.Control

/-- Lemma 4, Online Appendix p. 3: surplus is monotone in disclosure probability. -/
theorem lemma_4 (P : Params) (hS : P.Standing) :
    (P.σ < 1 → MonotoneOn (CS P) (Set.Icc (0 : ℝ) 1) ∧
      (0 < P.α → P.α < 1 → StrictMonoOn (CS P) (Set.Icc (0 : ℝ) 1))) ∧
    (1 < P.σ → AntitoneOn (CS P) (Set.Icc (0 : ℝ) 1) ∧
      (0 < P.α → P.α < 1 → StrictAntiOn (CS P) (Set.Icc (0 : ℝ) 1))) := by sorry

end PrivacyQueue.Control
