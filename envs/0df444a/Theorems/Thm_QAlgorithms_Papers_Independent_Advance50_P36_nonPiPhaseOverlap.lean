-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P36_nonPiPhaseOverlap
-- name    : QAlgorithms.Papers.Independent.Advance50.P36.nonPiPhaseOverlap
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T13:53:55.456087+00:00
-- url     : https://prove2.me/theorems/6539389b-3b91-4426-9485-15850c91815b
-- title:
--   Nonzero overlap away from pi in one phase period
-- statement:
--   Let $\alpha\ne0$ be a finite complex amplitude, let $\kappa=e^{-2|\alpha|^2}$, and let $\Psi_2=(|\alpha,\alpha\rangle-|-\alpha,-\alpha\rangle)/\sqrt{2(1-\kappa^2)}$ be the canonical odd quasi-Bell vector on the full two-mode Fock space. For a phase representative $0\leq\theta<2\pi$ with $\theta\ne\pi$, let $U_B(\theta)=\exp(-i\theta N_B)$ act on mode $B$. The coherent factors are canonically realized, both the input and rotated output have unit norm, and
--   $$
--   \left|\langle\Psi_2|(I_A\otimes U_B(\theta))\Psi_2\rangle\right|>0.
--   $$
--   Thus within one phase period only the pi rotation produces an orthogonal output from this family.
--
--   **Formalization Note** Printed Eq. (17) says only $\theta\ne\pi$. On unrestricted real angles it is false at $\theta=3\pi$. The one-period domain is an explicit source correction, as is the missing $i$ in Eq. (8); both require independent moderation.
-- source:
--   Error free Quantum Reading by Quasi Bell State of Entangled Coherent States, arXiv:1108.4163v2, PDF p. 3, §IV, Eq.(17), with explicit one-period correction

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P36

open QAlgorithms.Papers.Independent.Frontier30.P21
  (WordFock coherentWord CoherentWordRealized binaryErrorValues)

open scoped Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.3, Eq.(17), corrected to one phase period: printed theta != pi is
false on unrestricted real angles (theta=3*pi gives the same channel as pi).
We use 0 <= theta < 2*pi and theta != pi. Also correct the missing i in Eq.(8)
on p.2 as required by Eqs.(12),(15). These corrections require independent
moderation; the literal unrestricted assertion is recorded in MODERATION_NOTES.md. -/
theorem nonPiPhaseOverlap (alpha : ℂ) (halpha : alpha ≠ 0)
    (theta : ℝ) (htheta0 : 0 ≤ theta) (hthetaPeriod : theta < 2 * Real.pi)
    (hthetaPi : theta ≠ Real.pi) :
    QuasiBellCoherentRealized alpha ∧ ‖quasiBellState alpha 1‖ = 1 ∧
    ‖modeBPhaseShift theta (quasiBellState alpha 1)‖ = 1 ∧
    0 < ‖inner (𝕜 := ℂ) (quasiBellState alpha 1)
      (modeBPhaseShift theta (quasiBellState alpha 1))‖ := by sorry

end QAlgorithms.Papers.Independent.Advance50.P36

end
