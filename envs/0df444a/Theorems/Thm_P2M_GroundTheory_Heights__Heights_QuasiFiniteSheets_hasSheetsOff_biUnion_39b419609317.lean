-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_biUnion_39b419609317
-- name    : P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_biUnion_39b419609317
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:15:56.587802+00:00
-- url     : https://prove2.me/theorems/618b415e-60c0-5ee5-bbda-500f2696ba85
-- title:
--   P2 M Ground Theory Heights  Heights Quasi Finite Sheets has Sheets Off bi Union 39b419609317: P2 M Ground Theory Heights  Heights Quasi Finite Sheets has Sheets Off bi Union 39b419609317
-- statement:
--   The P2 M Ground Theory Heights  Heights Quasi Finite Sheets has Sheets Off bi Union 39b419609317 construction uses the P2 M Ground Theory Heights  Heights Quasi Finite Sheets has Sheets Off bi Union 39b419609317 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PQuasiFiniteSheets.lean#L73-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PQuasiFiniteSheets.lean#L73-L96

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

theorem P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_biUnion_39b419609317 (F : Finset (Ideal (MvPolynomial (Fin n) ℂ))) (A : Matrix (Fin d) (Fin n) ℂ)
    (hsh : ∀ Q ∈ F, ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ HasSheetsOff (ComplexSets.zeroSet Q) A c)
    (hpair : ∀ Q ∈ F, ∀ Q' ∈ F, Q ≠ Q' → ∃ e : MvPolynomial (Fin d) ℂ, e ≠ 0 ∧
      ∀ x ∈ ComplexSets.zeroSet Q ∩ ComplexSets.zeroSet Q', eval (A.mulVec x) e = 0) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ HasSheetsOff (⋃ Q ∈ F, ComplexSets.zeroSet Q) A c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«QuasiFiniteSheets».«hasSheetsOff_biUnion» := P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_biUnion_39b419609317
