-- Prove2me | Theorems.Thm_RightRepair_Equilibrium_table_G1
-- name    : RightRepair.Equilibrium.table_G1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:23.811531+00:00
-- url     : https://prove2.me/theorems/3c85ec28-224a-4676-958a-c6e55918e3d1
-- title:
--   Table G.1, OA p. 24 — optimal prices when independent repair costs at least δ
-- statement:
--   Suppose $c_I\ge\delta$ and the standing assumptions hold. Table G.1 gives three optimal outcomes as production cost $c$ rises: no repair for $c<\underline c$, partial repair for $\underline c\le c<\bar c$, and full repair for $\bar c\le c$. The new and used prices and repair probabilities in each case are exactly the Table G.1 formulas, and each outcome attains at least the profit of every admissible competing equilibrium.
--
--   In the partial-repair interval, $p_n=(c+1+\delta(1-f))/2$, $p_r=p_u=(\delta+c_M)/2$, and $\alpha=\hat\alpha(p_n,p_r)$. Its repair probability is strictly between zero and one when $\underline c<c<\bar c$.
--
--   **Formalization Note** At the printed left endpoint $c=\underline c$, $\hat\alpha=0$, so the strict claim in Table G.1 is made only in the open interval. The statement still asserts optimality at that endpoint. Assumption 1 excludes the table's $c_M\ge\delta$ row. The nonnegative unit-cost pins, the zero-price excess-supply equilibrium corner, and the `none` encoding of $p_r=\infty$ are part of the shared model.
-- source:
--   Jin, Yang & Zhu, Right to Repair: Pricing, Welfare, and Environmental Implications, authors' manuscript of Management Science (2022), doi:10.1287/mnsc.2022.4401 (PDF sha256 b869b33a…1763), OA p. 24, Table G.1 (PDF 57)

import Mathlib
import Definitions.Def_RightRepair_Equilibrium_Setting

namespace RightRepair.Equilibrium

theorem table_G1 (P : Params) (hP : Standing P)
    (hI : P.δ ≤ P.cI) :
    (P.c < cLow P →
      OptimalOutcome P (pnNo P) none (puNo P) 0) ∧
    (cLow P ≤ P.c → P.c < cBar P →
      OptimalOutcome P (pnNo P) (some ((P.δ + P.cM) / 2))
        ((P.δ + P.cM) / 2)
        (alphaHat P (pnNo P) ((P.δ + P.cM) / 2))) ∧
    (cLow P < P.c → P.c < cBar P →
      0 < alphaHat P (pnNo P) ((P.δ + P.cM) / 2) ∧
      alphaHat P (pnNo P) ((P.δ + P.cM) / 2) < 1) ∧
    (cBar P ≤ P.c →
      OptimalOutcome P (pnFull P) (some 0) (puFull P) 1) := by sorry

end RightRepair.Equilibrium
