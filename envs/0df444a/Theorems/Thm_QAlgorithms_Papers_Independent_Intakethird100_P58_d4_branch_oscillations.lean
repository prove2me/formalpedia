-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P58_d4_branch_oscillations
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P58.d4_branch_oscillations
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:58:11.180357+00:00
-- url     : https://prove2.me/theorems/50d13a9e-0022-41bb-89a3-77d18509df69
-- title:
--   Reported shrinking oscillations of the D4 shooting families
-- statement:
--   For the physical D4 reduced equation there exist regular disk profiles indexed by their axis depth $s\in(0,1)$, with boundary radii $\rho_D(s)$, and regular cylinder profiles indexed by their endpoint radii $t>0$, with boundary radii $\rho_C(t)$. The radius functions are continuous on their parameter intervals. The numerical study reported in the source finds a common finite $\rho_c>0$ with
--
--   $$
--   \rho_D(s)\longrightarrow\rho_c\quad(s\to1^-),\qquad
--   \rho_C(t)\longrightarrow\rho_c\quad(t\to0^+),
--   $$
--
--   and both radius functions take values strictly above and strictly below $\rho_c$ in every punctured neighborhood of their limiting parameter.
--
--   Finite limiting radius together with these repeated crossings is the qualitative diminishing-envelope interpretation of the reported oscillations. No decay rate, exact critical decimal, or exhaustive count of solutions at a prescribed radius is asserted.
-- source:
--   Topological Entanglement Entropy and Holography, arXiv:0805.1891v2, PDF p. 17, §4.1, Figs.8–9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P58

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P58

open Set Filter MeasureTheory

open scoped Topology

/-- PDF pp.17--18: the reported numerical shrinking oscillations of the D4
shooting families. This records a qualitative numerical finding of the source,
not a certified rate or an assertion of exactly two solutions at a fixed radius. -/
theorem d4_branch_oscillations :
    ∃ (R : ℝ → ℝ) (D C : ℝ → ℝ → ℝ) (critical : ℝ),
      0 < critical ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, IsDisk .d4 (R s) s (D s)) ∧
      (∀ t : ℝ, 0 < t → IsCylinder .d4 (C t 0) (C t) ∧ C t 1 = t) ∧
      ContinuousOn R (Ioo (0 : ℝ) 1) ∧
      ContinuousOn (fun t => C t 0) (Ioi (0 : ℝ)) ∧
      ShrinkingOscillations R (Ioo 0 1) 1 critical ∧
      ShrinkingOscillations (fun t => C t 0) (Ioi 0) 0 critical := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P58

end
