-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DivLin_baseChange_mul__56c41815aef1
-- name    : P2M_GlobalTheory_DivLin_baseChange_mul__56c41815aef1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:33.766824+00:00
-- url     : https://prove2.me/theorems/fadef853-9295-4619-a90b-0d7625ec2de3
-- title:
--   P2 M Global Theory Div Lin base Change mul  56c41815aef1: P2 M Global Theory Div Lin base Change mul  56c41815aef1
-- statement:
--   The P2 M Global Theory Div Lin base Change mul  56c41815aef1 construction uses the P2 M Global Theory Div Lin base Change mul  56c41815aef1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L69-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.DivLin
variable {O : Type} [CommRing O] {H : Type} [AddCommGroup H] [Module O H] {I : Type} [Fintype I]
  (R : Type) [CommRing R] [Algebra O R]

theorem P2M_GlobalTheory_DivLin_baseChange_mul__56c41815aef1 (f g : Module.End O H) : (f * g).baseChange R = f.baseChange R * g.baseChange R := by sorry

alias «GlobalTheory».«DivLin».«baseChange_mul'» := P2M_GlobalTheory_DivLin_baseChange_mul__56c41815aef1
