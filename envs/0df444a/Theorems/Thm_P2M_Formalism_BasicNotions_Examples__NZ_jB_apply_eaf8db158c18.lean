-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_jB_apply_eaf8db158c18
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_jB_apply_eaf8db158c18
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:49:42.140803+00:00
-- url     : https://prove2.me/theorems/fa7fb658-80b0-4950-9ff7-23b55303f952
-- title:
--   P2 M Formalism Basic Notions Examples  NZ j B apply eaf8db158c18: P2 M Formalism Basic Notions Examples  NZ j B apply eaf8db158c18
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ j B apply eaf8db158c18 construction uses the P2 M Formalism Basic Notions Examples  NZ j B apply eaf8db158c18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L79-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L79-L79

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_jB_apply_eaf8db158c18 (x : Fin n → K) : jB σ b x = ∑ i, σ (x i) • b i := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«jB_apply» := P2M_Formalism_BasicNotions_Examples__NZ_jB_apply_eaf8db158c18
