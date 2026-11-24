-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_jB_norm_5b7b434168e4
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_jB_norm_5b7b434168e4
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:51:15.63679+00:00
-- url     : https://prove2.me/theorems/e1ce97da-6219-4a61-87b6-a8bf67cd36dd
-- title:
--   P2 M Formalism Basic Notions Examples  NZ j B norm 5b7b434168e4: P2 M Formalism Basic Notions Examples  NZ j B norm 5b7b434168e4
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ j B norm 5b7b434168e4 construction uses the P2 M Formalism Basic Notions Examples  NZ j B norm 5b7b434168e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L139-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L139-L143

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_jB_norm_5b7b434168e4 (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (stdH K n).b (stdH K n).X (InfinitePlace.mk σ) x = ‖jB σ b x‖ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«jB_norm» := P2M_Formalism_BasicNotions_Examples__NZ_jB_norm_5b7b434168e4
