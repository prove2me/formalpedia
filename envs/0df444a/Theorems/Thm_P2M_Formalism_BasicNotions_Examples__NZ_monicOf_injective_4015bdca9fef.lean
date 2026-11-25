-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_monicOf_injective_4015bdca9fef
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_monicOf_injective_4015bdca9fef
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:09.68154+00:00
-- url     : https://prove2.me/theorems/e72b6cec-bd3a-4416-bff7-36b1611c964f
-- title:
--   P2 M Formalism Basic Notions Examples  NZ monic Of injective 4015bdca9fef: P2 M Formalism Basic Notions Examples  NZ monic Of injective 4015bdca9fef
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ monic Of injective 4015bdca9fef construction uses the P2 M Formalism Basic Notions Examples  NZ monic Of injective 4015bdca9fef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeE.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeE.lean#L11-L16

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms NumberField IsDedekindDomain

theorem P2M_Formalism_BasicNotions_Examples__NZ_monicOf_injective_4015bdca9fef {K : Type} [Field K] {N : ℕ} : Function.Injective (monicOf (K := K) (N := N)) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«monicOf_injective» := P2M_Formalism_BasicNotions_Examples__NZ_monicOf_injective_4015bdca9fef
