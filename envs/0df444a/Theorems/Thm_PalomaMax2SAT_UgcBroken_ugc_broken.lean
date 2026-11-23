-- Prove2me | Theorems.Thm_PalomaMax2SAT_UgcBroken_ugc_broken
-- name    : PalomaMax2SAT.UgcBroken.ugc_broken
-- status  : Proved
-- author  : @vegafrank
-- created : 2026-11-23T01:32:21.912808+00:00
-- url     : https://prove2.me/theorems/ac0b6f98-aa74-4047-a83b-446fa3307e21
-- title:
--   The Unique Games barrier is exceeded on the three-occurrence Horn class (83/84 above 0.94616 and 0.94017)
-- statement:
--   Let $\beta^\star=0.94016567$ and $\alpha^*=0.94615981$ be the Unique Games thresholds for MAX 2-SAT and weighted MAX-$\{1,2\}$-HORN-SAT. Then $\beta^\star<\alpha^*<\tfrac{83}{84}$ and $\alpha^*<\tfrac{19}{20}$; for every $d\ge6$, $19(3d+3)<20(3d+2)$, i.e. $\tfrac{3d+2}{3d+3}>\tfrac{19}{20}>\alpha^*$; and for every $D\ge3$, every $D$-regular graph $G$ with a port labelling on $n$ vertices and $m$ edges, with independence number $\alpha$, and every independent set $I$ with $6\alpha\le7|I|$, the assignment obtained from $I$ satisfies $$84\cdot\operatorname{sat}(T_G)\ \ge\ 83\,\bigl((D+1)n+m+\alpha\bigr),$$ that is, at least $83/84$ of the optimum $(D+1)n+m+\alpha$ of the three-occurrence Horn formula $T_G$. For $D=3$ the hypothesis $6\alpha\le7|I|$ is the independent-set size guaranteed by the Berman--Fujito cubic-MIS algorithm (item (3) of Theorem `thm:ugc-broken`); the guarantee itself is not part of the statement. The Unique Games thresholds quantify over all instances, so the statement concerns a bounded-occurrence class and is consistent with the Unique Games Conjecture. The bounded-occurrence guarantee of Ghoshal--Huang--Lee--Makarychev--Makarychev (items (1) and (2)) is cited in the paper and is not formalized.
-- source:
--   https://github.com/frankvegadelgado/paloma/blob/1d606664f7d6df86847888aeda94cf638e65e38a/doc/paper.tex#L221

import Mathlib
import Definitions.Def_PalomaMax2SAT_DegreeFormula
open PalomaMax2SAT.DegreeFormula

theorem PalomaMax2SAT.UgcBroken.ugc_broken :
    (((94016567 : ℚ) / 100000000 < 94615981 / 100000000 ∧
        (94615981 : ℚ) / 100000000 < 83 / 84) ∧
      (94615981 : ℚ) / 100000000 < 19 / 20) ∧
    (∀ d : ℕ, 6 ≤ d → 19 * (3 * d + 3) < 20 * (3 * d + 2)) ∧
    ∀ {D n m alpha : ℕ} (G : PortGraph D n m) (_ : 3 ≤ D)
      (_ : IsIndependenceNumber G alpha) (I : Finset (Fin n)) (_ : Independent G I)
      (_ : 6 * alpha ≤ 7 * I.card),
      83 * ((D + 1) * n + m + alpha) ≤
        84 * satCount G (assignmentOfIndependent I : Fin n → Fin (D + 1) → Bool) := by sorry
