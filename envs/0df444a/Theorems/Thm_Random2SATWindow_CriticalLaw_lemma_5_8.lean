-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_lemma_5_8
-- name    : Random2SATWindow.CriticalLaw.lemma_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:57.588011+00:00
-- url     : https://prove2.me/theorems/67c0b108-3f75-494e-a6e8-f386df18840e
-- title:
--   Lemma 5.8 — subcritical witness bound $\sum_{q\ge h}\pi_q(-t)\le C_ht^{-3h}$
-- statement:
--   For each fixed integer $h\ge1$ there is a constant $C_h$ such that
--   $$\sum_{q\ge h}\pi_q(-t)\le C_ht^{-3h}\qquad(t\ge1).\qquad(142)$$
--
--   Differences from the source:
--   - encoding: Σ_{q ≥ h} π_q(−t) → Summable (q ↦ π_{q+h}(−t)) ∧ Σ' q, π_{q+h}(−t) ≤ Ch / t^{3h}; reason: summability is stated so that the tsum is the series
--   - encoding: π_q(x) given by the integral (126) → piQC q x : ℂ is (126) verbatim; piQ q x = Re piQC q x, fProfile x = Σ' q, piQ q x; reason: (126) is a complex integral; Theorem 5.1(i) (theorem_5_1_i) states it is real
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), Lemma 5.8, printed p. 56 (PDF 58); proof printed pp. 56–57 (PDF 58–59)

import Mathlib
import Definitions.Def_Random2SATWindow_CriticalLaw_Formulas
import Definitions.Def_Random2SATWindow_CriticalLaw_Airy
import Definitions.Def_Random2SATWindow_CriticalLaw_Hadamard
import Definitions.Def_Random2SATWindow_CriticalLaw_Strata
import Definitions.Def_Random2SATWindow_CriticalLaw_Saddle
import Definitions.Def_Random2SATWindow_CriticalLaw_PureLiteral

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace Random2SATWindow.CriticalLaw

/-- **Lemma 5.8** (subcritical witness bound, printed p. 56 / PDF 58). For each fixed integer
`h ≥ 1` there is a constant `C_h` such that `Σ_{q ≥ h} π_q(-t) ≤ C_h t^{-3h}` for `t ≥ 1` (142). -/
theorem lemma_5_8 (h : ℕ) (hh : 1 ≤ h) :
    ∃ Ch : ℝ, ∀ t : ℝ, 1 ≤ t →
      Summable (fun q : ℕ => piQ (q + h) (-t)) ∧
      ∑' q : ℕ, piQ (q + h) (-t) ≤ Ch / t ^ (3 * h) := by sorry

end Random2SATWindow.CriticalLaw
