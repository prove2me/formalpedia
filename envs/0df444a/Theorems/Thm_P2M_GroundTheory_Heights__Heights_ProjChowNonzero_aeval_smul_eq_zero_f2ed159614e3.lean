-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_smul_eq_zero_f2ed159614e3
-- name    : P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_smul_eq_zero_f2ed159614e3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:20.757365+00:00
-- url     : https://prove2.me/theorems/d70ea87f-9a25-59f6-bdc3-f4ad48a6d033
-- title:
--   P2 M Ground Theory Heights  Heights Proj Chow Nonzero aeval smul eq zero f2ed159614e3: P2 M Ground Theory Heights  Heights Proj Chow Nonzero aeval smul eq zero f2ed159614e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Chow Nonzero aeval smul eq zero f2ed159614e3 construction uses the P2 M Ground Theory Heights  Heights Proj Chow Nonzero aeval smul eq zero f2ed159614e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L24-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjChowNonzero

theorem P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_smul_eq_zero_f2ed159614e3 {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {n : ℕ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsHomogIdeal W) {x : Fin n → Ω}
    (hx : ∀ q ∈ W, aeval x q = 0) (c : Ω) : ∀ q ∈ W, aeval (c • x) q = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjChowNonzero».«aeval_smul_eq_zero» := P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_smul_eq_zero_f2ed159614e3
