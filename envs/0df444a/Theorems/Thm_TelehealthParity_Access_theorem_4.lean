-- Prove2me | Theorems.Thm_TelehealthParity_Access_theorem_4
-- name    : TelehealthParity.Access.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:00.703072+00:00
-- url     : https://prove2.me/theorems/1baf51b7-4692-4aaf-bda4-db9fa7f46857
-- title:
--   Theorem 4 — $F(r,\theta)$ decreasing on $[0,\theta^T)$, affine on $[\theta^T,\theta^O)$, concave on $[\theta^O,\bar\theta)$, zero on $[\bar\theta,1]$
-- statement:
--   Under the standing assumptions with $R>0$, let $q$ be admissible and let $r>0$ be the telehealth reimbursement. Then the provider's revenue rate $\theta\mapsto F(r,\theta)$ of (23)
--   1. is strictly decreasing on $[0,\theta^T)$;
--   2. is affine on $[\theta^T,\theta^O)$: there are $a,b$ with $F(r,\theta)=a\theta+b$ for all $\theta\in[\theta^T,\theta^O)$;
--   3. is concave on $[\theta^O,\bar\theta)$;
--   4. vanishes on $[\bar\theta,1]$:
--   $$F(r,\theta)=0\qquad(\bar\theta\le\theta\le 1).$$
--
--   This shape result reduces the provider's choice of $\theta$ to comparing a few candidate points (Corollary 1).
--
--   **Formalization Note** The paper allows $R\ge 0$; strict decrease on $[0,\theta^T)$ needs $R>0$ (the slope there is $-R\mu$), so $R>0$ is an added hypothesis. "Linear in θ" is read as affine. The paper's "Assume q > 0" is part of admissibility.
-- source:
--   Çakıcı and Mills, Telehealth in Acute Care: Pay Parity and Patient Access, SSRN working paper (version of August 19, 2024), p. 16, Theorem 4; proof Appendix C, EC p. 8 (PDF 41)

import Mathlib
import Definitions.Def_TelehealthParity_Access_Setting

namespace TelehealthParity.Access

theorem theorem_4 (p : Params) (hp : p.Standing) (hR : 0 < p.R) (q : ℝ) (hq : Admissible p q)
    (r : ℝ) (hr : 0 < r) :
    StrictAntiOn (revenue p q r) (Set.Ico 0 (thetaT p q)) ∧
      (∃ a b : ℝ, ∀ θ ∈ Set.Ico (thetaT p q) (thetaO p q), revenue p q r θ = a * θ + b) ∧
      ConcaveOn ℝ (Set.Ico (thetaO p q) (thetaBar p q)) (revenue p q r) ∧
      ∀ θ ∈ Set.Icc (thetaBar p q) 1, revenue p q r θ = 0 := by sorry

end TelehealthParity.Access
