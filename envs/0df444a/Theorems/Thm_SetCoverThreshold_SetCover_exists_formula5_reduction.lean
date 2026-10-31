-- Prove2me | Theorems.Thm_SetCoverThreshold_SetCover_exists_formula5_reduction
-- name    : SetCoverThreshold.SetCover.exists_formula5_reduction
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T19:43:24.209025+00:00
-- url     : https://prove2.me/theorems/74f0a2d0-0dca-48ac-a23e-3c25ac97b8fc
-- title:
--   Papadimitriou–Yannakakis bounded-degree reduction to 3CNF-5
-- statement:
--   Papadimitriou–Yannakakis degree reduction from 3CNF-$B$ to 3CNF-5 (`Formula5`), preserving satisfiability and the constant-factor unsatisfiability gap in polynomial time: for any variable bound $B$ and unsatisfiability gap $\varepsilon_0 > 0$, there exists $\varepsilon > 0$ and a polynomial-time reduction $g$ mapping 3CNF-$B$ formulas to 3CNF-5 formulas such that satisfiable formulas remain satisfiable, and formulas where at most a $(1-\varepsilon_0)$ fraction of clauses can be satisfied are mapped to formulas where at most a $(1-\varepsilon)$ fraction can be satisfied (Papadimitriou and Yannakakis 1991; Feige 1998, Proposition 2.1.2).
-- source:
--   Papadimitriou and Yannakakis 1991; Feige 1998, A Threshold of ln n for Approximating Set Cover, J. ACM 45(4): 634–652, Proposition 2.1.2

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_SetCoverThreshold_SetCover_Formula

namespace SetCoverThreshold.SetCover

/-- Papadimitriou–Yannakakis degree reduction from 3CNF-`B` to 3CNF-5 (`Formula5`),
preserving satisfiability and the constant-factor unsatisfiability gap in polynomial time. -/
theorem exists_formula5_reduction (B : ℕ) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ (ε : ℝ) (g : CookPvsNP.CNF → Formula5)
      (g_enc : List CookPvsNP.SatSym → List CookPvsNP.SatSym),
      0 < ε ∧
      CookPvsNP.PolyTimeComputable g_enc ∧
      (∀ F, (Is3CNFB B F ∧ F.Satisfiable) ∨ (Is3CNFB B F ∧ AtMostFracSat (1 - ε₀) F) →
        CookPvsNP.encodeCNF (g F).toCNF = g_enc (CookPvsNP.encodeCNF F)) ∧
      (∀ F, Is3CNFB B F ∧ F.Satisfiable → (g F).toCNF.Satisfiable) ∧
      (∀ F, Is3CNFB B F ∧ AtMostFracSat (1 - ε₀) F → AtMostFracSat (1 - ε) (g F).toCNF) := by
  sorry

end SetCoverThreshold.SetCover
