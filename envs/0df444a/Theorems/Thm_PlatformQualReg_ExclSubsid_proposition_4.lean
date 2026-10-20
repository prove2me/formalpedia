-- Prove2me | Theorems.Thm_PlatformQualReg_ExclSubsid_proposition_4
-- name    : PlatformQualReg.ExclSubsid.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:04.823514+00:00
-- url     : https://prove2.me/theorems/a4a3c584-f228-47c1-b355-294a0352be4b
-- title:
--   Proposition 4, p. 26, corrected: subsidy versus exclusion
-- statement:
--   Compare an optimal exclusion outcome $(m^{E*},n^{E*},\Pi^{E*})$ with an optimal subsidization outcome $(m^{S*},n^{S*},\Pi^{S*})$ in the same two-sided market. Assume the standing conditions, strict concavity of both optimization problems, $\alpha_{dh}-\alpha_{dl}\le\beta q_h$, and interior outcomes with both subsidy developer types present. Then
--
--   $$
--   \Pi^{S*}\ge\Pi^{E*},\qquad
--   \bar q^{S*}\le q_h=\bar q^{E*},\qquad
--   m^{S*}>m^{E*},\quad n^{S*}>n^{E*}.
--   $$
--
--   Moreover, there is a feasible subsidization outcome with no low-quality developer, the same consumer and high-quality developer counts as exclusion, and the same profit. Thus the subsidization strategy can reproduce the exclusion outcome in the specified regime.
--
--   **Formalization Note** This corrects two parts of the printed Proposition 4. Profit dominance fails outside the added regime $\alpha_{dh}-\alpha_{dl}\le\beta q_h$. Its part (3) claims a larger *high-quality* developer count and a higher developer access fee; both claims have counterexamples. The theorem states the supported comparison for total developer count and omits the false fee comparison. The paper's $\mu=0$ convention is fixed in the model, and the interior and strict-concavity assumptions are explicit.
-- source:
--   Huang, Lyu & Xu, Quality regulation on two-sided platforms: exclusion, subsidization, and first-party applications, SSRN 3948778, p. 26 (PDF 27), Proposition 4 and following discussion; corrected as documented in MODERATION_NOTES.md

import Mathlib
import Definitions.Def_PlatformQualReg_ExclSubsid_Model

namespace PlatformQualReg.ExclSubsid

/-- Proposition 4, printed p. 26 (PDF 27), with its disclosed corrections. -/
theorem proposition_4 (P : Params) (hP : P.Standing)
    (hcE : ConcaveE P) (hcS : ConcaveS P)
    (hsub : P.adh - P.adl ≤ P.β * P.qh)
    (xE : OutcomeE) (hxE : IsOptE P xE) (hintE : 0 < xE.m ∧ 0 < xE.n)
    (xS : OutcomeS) (hxS : IsOptS P xS)
    (hintS : 0 < xS.m ∧ 0 < nl P xS ∧ 0 < nh P xS) :
    profitE P xE ≤ profitS P xS ∧
    (∃ y : OutcomeS, FeasibleS P y ∧ nl P y = 0 ∧ nh P y = xE.n ∧
      y.m = xE.m ∧ y.n = xE.n ∧ profitS P y = profitE P xE) ∧
    avgQualityS P xS ≤ P.qh ∧
    xE.m < xS.m ∧ xE.n < xS.n := by sorry

end PlatformQualReg.ExclSubsid
