-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_union_47b1eb91459a
-- name    : P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_union_47b1eb91459a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:16:08.040798+00:00
-- url     : https://prove2.me/theorems/690661fd-257f-49ec-901f-25c52f7462ad
-- title:
--   P2 M Ground Theory Heights  Heights Quasi Finite Sheets has Sheets Off union 47b1eb91459a: P2 M Ground Theory Heights  Heights Quasi Finite Sheets has Sheets Off union 47b1eb91459a
-- statement:
--   The P2 M Ground Theory Heights  Heights Quasi Finite Sheets has Sheets Off union 47b1eb91459a construction uses the P2 M Ground Theory Heights  Heights Quasi Finite Sheets has Sheets Off union 47b1eb91459a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PQuasiFiniteSheets.lean#L32-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PQuasiFiniteSheets.lean#L32-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimePairMeetImage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PQuasiFiniteSheets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.QuasiFiniteSheets
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_union_47b1eb91459a {S T : Set (Fin n → ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {c c' e : MvPolynomial (Fin d) ℂ} (h₁ : HasSheetsOff S A c) (h₂ : HasSheetsOff T A c')
    (he : ∀ x ∈ S ∩ T, eval (A.mulVec x) e = 0) : HasSheetsOff (S ∪ T) A (c * c' * e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«QuasiFiniteSheets».«hasSheetsOff_union» := P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_union_47b1eb91459a
