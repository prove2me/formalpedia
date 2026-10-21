-- Prove2me | Theorems.Thm_ShortTermism_Commitment_eq_A_26
-- name    : ShortTermism.Commitment.eq_A_26
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:07.341624+00:00
-- url     : https://prove2.me/theorems/9eaf7f1e-a152-44db-b9e8-d1c4cf82418d
-- title:
--   (A.26), §A.4.2, p. 49 — with a = a_u(δ), the maximum over e ∈ [0, ē] of the HJB integrand is attained at e_u(δ)
-- statement:
--   In the setting of the mission's model, assume the standing assumptions, let $f_u$ be the unlevered value solving (25) with the conditions of Proposition 3, and let $(a_u,e_u)$ be its effort policy. Then for every coupon $C$, every function $f$ and every $\delta\ge\underline\delta$, the maximum of the braces of (18) over short-term effort, with long-term effort held at $a_u(\delta)$, is attained at $e_u(\delta)$:
--   $$\max_{e\in[0,\bar e]} H_C\big(\delta,a_u(\delta),e,f'(\delta),f''(\delta)\big)=H_C\big(\delta,a_u(\delta),e_u(\delta),f'(\delta),f''(\delta)\big),$$
--   where $H_C$ is the braces of (18) for coupon $C$ (the maximum exists and equals the right-hand side).
--
--   The left-hand side is the right-hand side of the no-underinvestment equation (A.29) and the right-hand side is that of the no-overhang equation (A.27). This identity, the paper's display (A.26), is what makes the two boundary-value problems coincide.
--
--   **Formalization Note** The page's display (A.26) is written in condensed notation and has typographical slips (a factor $\delta$ is omitted from the effort terms, the term $-a_u(\delta)\hat B$ lacks the factor $e$, and "$-+\phi\delta f'(\delta)$" stands for $+\phi\delta f'(\delta)$); the statement is the corrected identity in the uncondensed form of (A.27) and (A.29).
-- source:
--   Hackbarth, Rivera & Wong, Optimal Short-Termism, ECGI Finance Working Paper 546/2018 (June 2021 version, SSRN 3060869), p. 49 (PDF 53), Appendix A.4.2, equation (A.26)

import Mathlib
import Definitions.Def_ShortTermism_Commitment_Model

namespace ShortTermism.Commitment

theorem eq_A_26 (P : Params) (hP : P.Standing) (fu au eu : ℝ → ℝ)
    (hv : IsUnleveredValue P fu) (hu : IsUnleveredPolicy P fu au eu)
    (C : ℝ) (f : ℝ → ℝ) (δ : ℝ) (hδ : P.dlow ≤ δ) :
    IsGreatest
      ((fun e => hjbIntegrand P C δ (au δ) e (deriv f δ) (deriv (deriv f) δ)) '' Set.Icc 0 P.ebar)
      (hjbIntegrand P C δ (au δ) (eu δ) (deriv f δ) (deriv (deriv f) δ)) := by sorry

end ShortTermism.Commitment
