-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_jB_inj_9ad1f419b94c
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_jB_inj_9ad1f419b94c
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:48:18.667599+00:00
-- url     : https://prove2.me/theorems/c6a643c7-e273-4ac7-b743-78d031e00645
-- title:
--   P2 M Formalism Basic Notions Examples  NZ j B inj 9ad1f419b94c: P2 M Formalism Basic Notions Examples  NZ j B inj 9ad1f419b94c
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ j B inj 9ad1f419b94c construction uses the P2 M Formalism Basic Notions Examples  NZ j B inj 9ad1f419b94c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L96-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L96-L97

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
variable {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)

theorem P2M_Formalism_BasicNotions_Examples__NZ_jB_inj_9ad1f419b94c : Function.Injective (jB σ b) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«jB_inj» := P2M_Formalism_BasicNotions_Examples__NZ_jB_inj_9ad1f419b94c
