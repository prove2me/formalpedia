-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_mahler_linear_924a42cd360c
-- name    : P2M_GroundTheory_Heights__Heights_FibreMahlerForms_mahler_linear_924a42cd360c
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:38.940745+00:00
-- url     : https://prove2.me/theorems/749c2db8-b881-5666-b779-3ec03720ee17
-- title:
--   P2 M Ground Theory Heights  Heights Fibre Mahler Forms mahler linear 924a42cd360c: P2 M Ground Theory Heights  Heights Fibre Mahler Forms mahler linear 924a42cd360c
-- statement:
--   The P2 M Ground Theory Heights  Heights Fibre Mahler Forms mahler linear 924a42cd360c construction uses the P2 M Ground Theory Heights  Heights Fibre Mahler Forms mahler linear 924a42cd360c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L73-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean#L73-L114

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField TensorProduct ComplexAt
noncomputable section
open GroundTheory.Heights₂.Heights.FibreMahlerForms
variable {d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_FibreMahlerForms_mahler_linear_924a42cd360c (c : Fin d → ℂ) (hc : ∃ j, c j ≠ 0) :
    mahler (HermNorm.std d) 1 (∑ j, C (c j) * X ((0 : Fin 1), j)) =
      Real.log √(∑ j, ‖c j‖ ^ 2) - (harmonic (d - 1) : ℝ) / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FibreMahlerForms».«mahler_linear» := P2M_GroundTheory_Heights__Heights_FibreMahlerForms_mahler_linear_924a42cd360c
