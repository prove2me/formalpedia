-- Prove2me | Theorems.Thm_PalomaMax2SAT_UgcBarrier_ugc_barrier
-- name    : PalomaMax2SAT.UgcBarrier.ugc_barrier
-- status  : Proved
-- author  : @vegafrank
-- created : 2026-11-22T13:34:37.67674+00:00
-- url     : https://prove2.me/theorems/0fd5566b-462b-4bbf-9091-d068db94488a
-- title:
--   Ratio $83/84$ above the Unique Games thresholds
-- statement:
--   Let $G$ be a $D$-regular graph with a port labelling, $D\ge1$, on $n$ vertices and $m$ edges, let $\alpha$ be its independence number and let $T_G$ be the three-occurrence Horn formula of the paper. Then $\tfrac{83}{84}>0.94615981>0.94016567$, and for every independent set $I$ with $18785\,\alpha\le 20000\,|I|$ the assignment obtained from $I$ satisfies $$84\cdot\operatorname{sat}(T_G)\ \ge\ 83\,\bigl((D+1)n+m+\alpha\bigr),$$ that is, at least $83/84$ of the optimum $(D+1)n+m+\alpha$ of $T_G$. The hypothesis on $I$ is the size guaranteed by a Goemans--Williamson cut lifted to the conflict graph (Theorem `thm:cutclass`); the cut guarantee itself is not part of the statement. The numbers $0.94615981$ and $0.94016567$ are the Unique Games thresholds of Brakensiek--Huang--Zwick and Lewin--Livnat--Zwick.
-- source:
--   https://github.com/frankvegadelgado/paloma/blob/5c464fdfa547ca94b1d42a8f33629ad256ec89e3/doc/paper.tex#L295

import Mathlib
import Definitions.Def_PalomaMax2SAT_DegreeFormula
open PalomaMax2SAT.DegreeFormula

theorem PalomaMax2SAT.UgcBarrier.ugc_barrier :
    ((94016567 : ℚ) / 100000000 < 94615981 / 100000000 ∧
      (94615981 : ℚ) / 100000000 < 83 / 84) ∧
    ∀ {D n m alpha : ℕ} (G : PortGraph D n m) (_ : 0 < D)
      (_ : IsIndependenceNumber G alpha) (I : Finset (Fin n)) (_ : Independent G I)
      (_ : 18785 * alpha ≤ 20000 * I.card),
      83 * ((D + 1) * n + m + alpha) ≤
        84 * satCount G (assignmentOfIndependent I : Fin n → Fin (D + 1) → Bool) := by sorry
