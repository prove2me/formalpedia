-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_controlled_phase_obstruction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.controlled_phase_obstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:01:43.55419+00:00
-- url     : https://prove2.me/theorems/d5857561-e282-4143-9072-45066b8d5896
-- title:
--   Appendix G2: sample density records cannot fix a controlled global phase
-- statement:
--   Let the ambient system be nonempty, $U$ unitary and $z$ a complex phase with $|z|=1$ and $z\ne1$. Every density record is invariant under replacing $U$ by $zU$:
--
--   $$U\rho U^\dagger=(zU)\rho(zU)^\dagger\quad\text{for every }\rho.$$
--
--   Nevertheless their controlled unitaries are not scalar-phase equivalent: no unit phase $w$ satisfies $(zU)^c=wU^c$. The identity control branch forces $w=1$, while the other branch retains $z$. This is an identifiability obstruction when only sample density copies and no coherent phase reference are supplied.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 28, Appendix G2: sample density records cannot fix a controlled global phase

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF p.28, G2 discussion: density records cannot distinguish global phases, but
nontrivial relative phase changes a systemControlled unitary. -/
theorem controlled_phase_obstruction [Nonempty I] (U : Matrix.unitaryGroup I ℂ)
    (z : ℂ) (hz : ‖z‖ = 1) (hne : z ≠ 1) :
    (∀ rho : Matrix I I ℂ, IsDensityMatrix rho →
      densityConjugation (z • (U : Matrix I I ℂ)) rho = densityConjugation (U : Matrix I I ℂ) rho) ∧
    ¬ ∃ w : ℂ, ‖w‖ = 1 ∧ systemControlled (z • (U : Matrix I I ℂ)) = w • systemControlled (U : Matrix I I ℂ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
