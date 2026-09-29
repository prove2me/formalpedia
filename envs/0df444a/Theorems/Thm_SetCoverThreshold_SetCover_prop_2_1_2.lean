-- Prove2me | Theorems.Thm_SetCoverThreshold_SetCover_prop_2_1_2
-- name    : SetCoverThreshold.SetCover.prop_2_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:55:51.629318+00:00
-- url     : https://prove2.me/theorems/57ad3bc0-986b-4df1-b0ed-8598faae11c9
-- title:
--   Proposition 2.1.2 — MAX 3SAT-5 is gap NP-hard (from Theorem 2.1.1)
-- statement:
--   Assume Theorem 2.1.1 (Arora et al. 1992; Papadimitriou–Yannakakis 1991): for some $B$ and $\varepsilon>0$ it is NP-hard to distinguish satisfiable 3CNF-B formulas from 3CNF-B formulas in which at most a $(1-\varepsilon)$-fraction of the clauses can be satisfied simultaneously.
--
--   Then there is $\varepsilon'>0$ such that it is NP-hard to distinguish between
--
--   $$\text{satisfiable 3CNF-5 formulas}\quad\text{and}\quad\text{3CNF-5 formulas in which at most a }(1-\varepsilon')\text{-fraction of the clauses can be satisfied simultaneously.}$$
--
--   Here a 3CNF-5 formula has $n$ variables and $5n/3$ clauses, every clause contains exactly three literals on three distinct variables, and every variable appears in exactly five clauses. This is the input problem of the multi-prover proof system of Section 2, whose regular structure the reduction to set cover uses.
--
--   **Formalization Note** NP-hardness is Karp style: every NP language maps in polynomial time (on Cook's one-tape machines) to 3CNF-5 formulas, members to satisfiable formulas and non-members to formulas that are far from satisfiable. Formulas are encoded as in `CookPvsNP_defs`.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 640, Proposition 2.1.2 (assuming Theorem 2.1.1, p. 639)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_SetCoverThreshold_SetCover_Formula

namespace SetCoverThreshold.SetCover

theorem prop_2_1_2 (h211 : Thm211) :
    ∃ ε : ℝ, 0 < ε ∧
      GapNPHard (fun φ : Formula5 => CookPvsNP.encodeCNF φ.toCNF)
        (fun φ => φ.toCNF.Satisfiable) (fun φ => AtMostFracSat (1 - ε) φ.toCNF) := by sorry

end SetCoverThreshold.SetCover
