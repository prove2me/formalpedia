-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_proof_79ef8cd0a48a
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_proof_79ef8cd0a48a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:43:46.284797+00:00
-- url     : https://prove2.me/theorems/0a411511-e4db-5711-b00d-1df1f062a3ed
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines proof 79ef8cd0a48a: P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines proof 79ef8cd0a48a
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines proof 79ef8cd0a48a construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines proof 79ef8cd0a48a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PGramDetermines.lean#L51-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PGramDetermines.lean#L51-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StGramDetermines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramDetermines
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open GroundTheory.Heights₂.Heights.FiniteCovolume.GramDetermines

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_proof_79ef8cd0a48a (h : HermitianForm F E W) : GramDetermines.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GramDetermines».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_proof_79ef8cd0a48a
