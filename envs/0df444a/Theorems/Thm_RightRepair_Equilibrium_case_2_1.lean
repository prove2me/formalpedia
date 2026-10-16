-- Prove2me | Theorems.Thm_RightRepair_Equilibrium_case_2_1
-- name    : RightRepair.Equilibrium.case_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:27.238086+00:00
-- url     : https://prove2.me/theorems/2c63be29-6759-4ce1-bad5-148025c1ca1a
-- title:
--   Case 2.1, OA pp. 26–31 — optimal outcomes for intermediate independent repair costs
-- statement:
--   Suppose $(\delta+c_M)/2\le c_I<\delta$. The proof's Case 2.1 gives the no-repair outcome when $c\le\underline c$, the partial-repair outcome when $\underline c<c<\bar c$, and the full-repair outcome when $\bar c\le c$. In each regime, the displayed new-product price, repair price, used-product price, and repair probability form an equilibrium that maximizes the manufacturer's profit against every admissible competing equilibrium.
--
--   In the partial-repair regime, $p_n=(c+1+\delta(1-f))/2$, $p_r=p_u=(\delta+c_M)/2$, and $0<\hat\alpha(p_n,p_r)<1$.
--
--   **Formalization Note** The full-repair price $p_r=0$ is one point on the source's optimal line. The nonnegative unit-cost pins, zero-price excess-supply corner, and `none` encoding of $p_r=\infty$ are part of the shared model.
-- source:
--   Jin, Yang & Zhu, Right to Repair: Pricing, Welfare, and Environmental Implications, authors' manuscript of Management Science (2022), doi:10.1287/mnsc.2022.4401 (PDF sha256 b869b33a…1763), OA pp. 26–31, Case 2.1 and three conclusions (PDF 59–64)

import Mathlib
import Definitions.Def_RightRepair_Equilibrium_Setting

namespace RightRepair.Equilibrium

theorem case_2_1 (P : Params) (hP : Standing P)
    (hI : (P.δ + P.cM) / 2 ≤ P.cI ∧ P.cI < P.δ) :
    (P.c ≤ cLow P →
      OptimalOutcome P (pnNo P) none (puNo P) 0) ∧
    (cLow P < P.c → P.c < cBar P →
      OptimalOutcome P (pnNo P) (some ((P.δ + P.cM) / 2))
        ((P.δ + P.cM) / 2)
        (alphaHat P (pnNo P) ((P.δ + P.cM) / 2)) ∧
      0 < alphaHat P (pnNo P) ((P.δ + P.cM) / 2) ∧
      alphaHat P (pnNo P) ((P.δ + P.cM) / 2) < 1) ∧
    (cBar P ≤ P.c →
      OptimalOutcome P (pnFull P) (some 0) (puFull P) 1) := by sorry

end RightRepair.Equilibrium
