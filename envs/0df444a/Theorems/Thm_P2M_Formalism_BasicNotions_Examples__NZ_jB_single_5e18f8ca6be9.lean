-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_jB_single_5e18f8ca6be9
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_jB_single_5e18f8ca6be9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:04:04.796033+00:00
-- url     : https://prove2.me/theorems/b29d09ab-1639-4419-b663-2d897d51731a
-- title:
--   P2 M Formalism Basic Notions Examples  NZ j B single 5e18f8ca6be9: P2 M Formalism Basic Notions Examples  NZ j B single 5e18f8ca6be9
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ j B single 5e18f8ca6be9 construction uses the P2 M Formalism Basic Notions Examples  NZ j B single 5e18f8ca6be9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L81-L86

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_jB_single_5e18f8ca6be9 (i : Fin n) : jB σ b (Pi.basisFun K (Fin n) i) = b i := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«jB_single» := P2M_Formalism_BasicNotions_Examples__NZ_jB_single_5e18f8ca6be9
