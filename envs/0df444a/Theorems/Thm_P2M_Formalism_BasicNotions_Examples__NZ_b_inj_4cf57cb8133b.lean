-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_b_inj_4cf57cb8133b
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_b_inj_4cf57cb8133b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:49:28.485392+00:00
-- url     : https://prove2.me/theorems/fd017b3a-7602-4f7c-8919-94f1298bafd0
-- title:
--   P2 M Formalism Basic Notions Examples  NZ b inj 4cf57cb8133b: P2 M Formalism Basic Notions Examples  NZ b inj 4cf57cb8133b
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ b inj 4cf57cb8133b construction uses the P2 M Formalism Basic Notions Examples  NZ b inj 4cf57cb8133b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L145-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L145-L147

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
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
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)

theorem P2M_Formalism_BasicNotions_Examples__NZ_b_inj_4cf57cb8133b : Function.Injective b := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«b_inj» := P2M_Formalism_BasicNotions_Examples__NZ_b_inj_4cf57cb8133b
