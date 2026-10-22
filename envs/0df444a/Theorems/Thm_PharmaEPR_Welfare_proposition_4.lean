-- Prove2me | Theorems.Thm_PharmaEPR_Welfare_proposition_4
-- name    : PharmaEPR.Welfare.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:29.574048+00:00
-- url     : https://prove2.me/theorems/df920aa9-4cc8-4cda-ab38-056ebff865ec
-- title:
--   Proposition 4 and Table 2, pp. 17–18 (α < 1/4, β < o_d/2, α + β ≤ 1) — welfare-maximizing EPR policy
-- statement:
--   Under the stated $\alpha<1/4$, $\beta<o_d/2$, and $\alpha+\beta\le1$ regime, the planner's EC and SR welfare maxima exist. With the appendix's fixed health-benefit and collection-cost thresholds, their attained values obey Table 2:
--
--   $$
--   \begin{array}{c|ccc}
--     &u_p<\bar u_p^{EC}&\bar u_p^{EC}\le u_p<\bar u_p^{SR}&u_p\ge\bar u_p^{SR}\\
--   k<\bar k& W_*^{EC}=W_*^{SR}&W_*^{EC}=W_*^{SR}&W_*^{EC}\le W_*^{SR}\\
--   k\ge\bar k& W_*^{EC}=W_*^{SR}&\multicolumn{2}{c}{\epsilon_e\ge\tilde\epsilon_e:\ W_*^{SR}\le W_*^{EC};\quad
--     \epsilon_e<\tilde\epsilon_e:\ W_*^{EC}\le W_*^{SR}}
--   \end{array}
--   $$
--
--   When $u_p\ge\bar u_p^{EC}$ and $k\ge\bar k$, a threshold $\tilde\epsilon_e$ works for every nonnegative environmental disutility while the other parameters stay fixed. At and above it, some welfare-maximizing EC outcome eliminates over-prescription, retaining Proposition 4's condition $\tilde\epsilon_e\ge\bar\epsilon_e^{EC}$. Weak inequalities allow both models to maximize welfare at a tie.
--
--   This is the policy-choice result of Proposition 4 and Table 2, expressed through welfare computed from the Section 3 game rather than an assumed closed form.
--
--   **Formalization Note** In this restricted regime $\bar u_p^{EC}<0\le u_p$, so the first column is vacuous. The appendix imposes $\alpha+\beta\le1$ for nonnegative producer profit. The goal also asserts attainment of both welfare optima as $\epsilon_e$ varies in the threshold clause.
-- source:
--   Alev, Atasu, Toktay & Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020-09-05 posting), pp. 17–18, Proposition 4 and Table 2; proof Online Appendix pp. 3–5

import Mathlib
import Definitions.Def_PharmaEPR_Welfare_Model

namespace PharmaEPR.Welfare

theorem proposition_4 (P : Params) (hP : Regime P) :
    IsGreatest (achievable P .EC) (optW P .EC) ∧
    IsGreatest (achievable P .SR) (optW P .SR) ∧
    (P.up < uEC P → optW P .EC = optW P .SR) ∧
    (uEC P ≤ P.up → P.up < uSR P → P.k < kBar P →
      optW P .EC = optW P .SR) ∧
    (uSR P ≤ P.up → P.k < kBar P →
      optW P .EC ≤ optW P .SR) ∧
    (uEC P ≤ P.up → kBar P ≤ P.k →
      ∃ epsilonT : ℝ, ∀ e : ℝ, 0 ≤ e →
        let Q : Params := { P with epsE := e }
        IsGreatest (achievable Q .EC) (optW Q .EC) ∧
        IsGreatest (achievable Q .SR) (optW Q .SR) ∧
        (epsilonT ≤ e →
          optW Q .SR ≤ optW Q .EC ∧
          optW Q .EC ∈ achievableNoOP Q .EC) ∧
        (e < epsilonT → optW Q .EC ≤ optW Q .SR)) := by sorry

end PharmaEPR.Welfare
