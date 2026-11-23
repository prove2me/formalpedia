-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_denseRange_emb_e16ca7438e57
-- name    : P2M_Formalism_BasicNotions_Examples__LB_denseRange_emb_e16ca7438e57
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:37.906668+00:00
-- url     : https://prove2.me/theorems/a8c7e6ac-9fb1-42eb-bf53-7161ea27ba85
-- title:
--   P2 M Formalism Basic Notions Examples  LB dense Range emb e16ca7438e57: P2 M Formalism Basic Notions Examples  LB dense Range emb e16ca7438e57
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB dense Range emb e16ca7438e57 construction uses the P2 M Formalism Basic Notions Examples  LB dense Range emb e16ca7438e57 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L12-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L12-L45

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise
variable (l : ℕ) [hl : Fact l.Prime]

theorem P2M_Formalism_BasicNotions_Examples__LB_denseRange_emb_e16ca7438e57 {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l) :
    DenseRange j := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«denseRange_emb» := P2M_Formalism_BasicNotions_Examples__LB_denseRange_emb_e16ca7438e57
