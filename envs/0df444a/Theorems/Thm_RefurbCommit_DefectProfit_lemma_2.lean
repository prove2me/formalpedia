-- Prove2me | Theorems.Thm_RefurbCommit_DefectProfit_lemma_2
-- name    : RefurbCommit.DefectProfit.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:51.523095+00:00
-- url     : https://prove2.me/theorems/90346793-24a1-49dd-871c-f76c9349c9fe
-- title:
--   Lemma 2, p. A-2 (PDF 35) — strategies ∅N∅ and N∅∅ are not optimal
-- statement:
--   Fix parameters satisfying the standing assumptions and a defect rate $\alpha>0$ at which the firm's subgame-perfect profit is positive, $\Pi^*(\alpha)>0$. Then a subgame-perfect outcome attaining $\Pi^*(\alpha)$ exists, and no such optimal outcome $(p_1,q_1,p_2,p_r)$ with second-period sales $(q_2,q_r)$ uses either
--
--   1. Strategy $\emptyset N\emptyset$: $q_1=q_r=0$ and $q_2>0$ (nothing in period 1, only the new product in period 2); or
--   2. Strategy $N\emptyset\emptyset$: $q_1>0$ and $q_2=q_r=0$ (the new product in period 1, nothing in period 2).
--
--   The lemma narrows the candidate equilibrium strategies to the five of Table 4 used in the analysis of Proposition 3.
--
--   **Formalization Note** The hypothesis $\Pi^*(\alpha)>0$ is the paper's restriction to the parameter region with positive two-period profit (p. 6), which the proof of part (b) uses. The existence of an optimal outcome is stated as a conjunct (the firm's problem (4.5) is a maximization), so that the second clause is not vacuous.
-- source:
--   Singh, Ramachandran & Subramanian, Intertemporal product management with strategic consumers: the value of defective product returns, accepted manuscript (MSOM, Dec. 2020; SSRN 2511424), p. A-2 (PDF 35), Lemma 2

import Mathlib
import Definitions.Def_RefurbCommit_DefectProfit_Model

namespace RefurbCommit.DefectProfit

/-- Lemma 2 (p. A-2): in the positive-profit region, an optimal subgame-perfect outcome
exists, and no optimal outcome uses Strategy ∅N∅ or Strategy N∅∅. -/
theorem lemma_2 (P : Params) (hP : P.Standing) (α : ℝ) (hα : 0 < α)
    (hpos : 0 < PiStar P α) :
    (∃ p1 q1 p2 pr, IsSPOutcome P α p1 q1 p2 pr ∧ totalProfit P α p1 q1 p2 pr = PiStar P α) ∧
    ∀ p1 q1 p2 pr, IsSPOutcome P α p1 q1 p2 pr → totalProfit P α p1 q1 p2 pr = PiStar P α →
      -- (a) Strategy ∅N∅ is not optimal
      ¬ (q1 = 0 ∧ qr P α q1 p2 pr = 0 ∧ 0 < q2 P α q1 p2 pr) ∧
      -- (b) Strategy N∅∅ is not optimal
      ¬ (0 < q1 ∧ q2 P α q1 p2 pr = 0 ∧ qr P α q1 p2 pr = 0) := by sorry

end RefurbCommit.DefectProfit
