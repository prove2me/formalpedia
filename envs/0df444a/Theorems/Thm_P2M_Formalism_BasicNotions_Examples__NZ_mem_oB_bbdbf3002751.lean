-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_mem_oB_bbdbf3002751
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_mem_oB_bbdbf3002751
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:55.237719+00:00
-- url     : https://prove2.me/theorems/98e6866c-d29f-4b62-8510-f6e4274c389b
-- title:
--   P2 M Formalism Basic Notions Examples  NZ mem o B bbdbf3002751: P2 M Formalism Basic Notions Examples  NZ mem o B bbdbf3002751
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ mem o B bbdbf3002751 construction uses the P2 M Formalism Basic Notions Examples  NZ mem o B bbdbf3002751 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L162-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L162-L173

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_mem_oB_bbdbf3002751 {O : Type} [CommRing O] (φ : O →+* ℂ) (x : V) :
    x ∈ (oB b φ).carrier ↔ ∃ c : Fin n → O, x = ∑ i, φ (c i) • b i := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«mem_oB» := P2M_Formalism_BasicNotions_Examples__NZ_mem_oB_bbdbf3002751
