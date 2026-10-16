-- Prove2me | Theorems.Thm_RightRepair_Equilibrium_proposition_1
-- name    : RightRepair.Equilibrium.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:35.993986+00:00
-- url     : https://prove2.me/theorems/9b8f87fc-dfe0-46d3-ab10-8141c6f3f460
-- title:
--   Proposition 1, p. 13 — optimal prices and resulting equilibrium in Table 1
-- statement:
--   In the identical-quality, zero-transaction-cost repair market under Assumption 1, the manufacturer's optimal new-product price, manufacturer repair price, used-product price, and consumer repair probability follow all seven rows of Table 1. When $c_I\ge(\delta+c_M)/2$, the production-cost regimes are $c\le\underline c$, $\underline c<c<\bar c$, and $\bar c\le c$. When $c_I<(\delta+c_M)/2$, they are $c<\hat c_1$, $\hat c_1\le c\le\hat c_2$, $\hat c_2<c<\hat c_3$, and $\hat c_3\le c$.
--
--   Every row gives an actual secondary-market equilibrium and a manufacturer's profit no smaller than that of any equilibrium under any admissible competing prices. The two partial-repair rows also assert $0<\hat\alpha<1$. The explicit prices, used prices, repair probabilities, and cutoffs are those of Table 1 and its appendix definitions.
--
--   **Formalization Note** A row asserts an optimal outcome, not uniqueness; adjacent rows can tie and full-repair optimal prices lie on a line. An unavailable repair service, printed as $p_r=\infty$, is `none`. The standing assumptions include disclosed $c,c_M\ge0$ unit-cost pins. Market clearing permits excess used-product supply at $p_u=0$; every competitor equilibrium is quantified over. The partial-repair bounds rule out a junk $0/0$ evaluation of $\hat\alpha$.
-- source:
--   Jin, Yang & Zhu, Right to Repair: Pricing, Welfare, and Environmental Implications, authors' manuscript of Management Science (2022), doi:10.1287/mnsc.2022.4401 (PDF sha256 b869b33a…1763), p. 13, Proposition 1; p. 14, Table 1; OA pp. 18–45 (PDF 51–78)

import Mathlib
import Definitions.Def_RightRepair_Equilibrium_Setting

namespace RightRepair.Equilibrium

theorem proposition_1 (P : Params) (hP : Standing P) :
    ((P.δ + P.cM) / 2 ≤ P.cI →
      (P.c ≤ cLow P →
        OptimalOutcome P (pnNo P) none (puNo P) 0) ∧
      (cLow P < P.c → P.c < cBar P →
        OptimalOutcome P (pnNo P) (some ((P.δ + P.cM) / 2))
          ((P.δ + P.cM) / 2)
          (alphaHat P (pnNo P) ((P.δ + P.cM) / 2)) ∧
        0 < alphaHat P (pnNo P) ((P.δ + P.cM) / 2) ∧
        alphaHat P (pnNo P) ((P.δ + P.cM) / 2) < 1) ∧
      (cBar P ≤ P.c →
        OptimalOutcome P (pnFull P) (some 0) (puFull P) 1)) ∧
    (P.cI < (P.δ + P.cM) / 2 →
      (P.c < cHat1 P →
        OptimalOutcome P (pnNo P) none (puNo P) 0) ∧
      (cHat1 P ≤ P.c → P.c ≤ cHat2 P →
        OptimalOutcome P (pnNoLowI P) none P.cI 0) ∧
      (cHat2 P < P.c → P.c < cHat3 P →
        OptimalOutcome P (pnPartialLowI P) (some P.cI) P.cI
          (alphaHat P (pnPartialLowI P) P.cI) ∧
        0 < alphaHat P (pnPartialLowI P) P.cI ∧
        alphaHat P (pnPartialLowI P) P.cI < 1) ∧
      (cHat3 P ≤ P.c →
        OptimalOutcome P (pnFull P) (some 0) (puFull P) 1)) := by sorry

end RightRepair.Equilibrium
