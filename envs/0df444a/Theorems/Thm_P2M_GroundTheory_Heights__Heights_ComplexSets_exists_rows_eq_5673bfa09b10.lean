-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_exists_rows_eq_5673bfa09b10
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_exists_rows_eq_5673bfa09b10
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:16:17.4776+00:00
-- url     : https://prove2.me/theorems/ee676cb8-cc00-5eb5-a57d-a9bde4776494
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets exists rows eq 5673bfa09b10: P2 M Ground Theory Heights  Heights Complex Sets exists rows eq 5673bfa09b10
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets exists rows eq 5673bfa09b10 construction uses the P2 M Ground Theory Heights  Heights Complex Sets exists rows eq 5673bfa09b10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericProjectionFinite.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericProjectionFinite.lean#L28-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericProjectionFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_exists_rows_eq_5673bfa09b10 {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) (A : Matrix (Fin d) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, (F * U).submatrix s id = A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«exists_rows_eq» := P2M_GroundTheory_Heights__Heights_ComplexSets_exists_rows_eq_5673bfa09b10
