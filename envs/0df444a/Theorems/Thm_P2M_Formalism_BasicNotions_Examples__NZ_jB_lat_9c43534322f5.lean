-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_jB_lat_9c43534322f5
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_jB_lat_9c43534322f5
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:48:46.076637+00:00
-- url     : https://prove2.me/theorems/b4fd91b1-0d4f-411a-a7d7-00fc47ed12d5
-- title:
--   P2 M Formalism Basic Notions Examples  NZ j B lat 9c43534322f5: P2 M Formalism Basic Notions Examples  NZ j B lat 9c43534322f5
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ j B lat 9c43534322f5 construction uses the P2 M Formalism Basic Notions Examples  NZ j B lat 9c43534322f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L177-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L177-L195

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_jB_lat_9c43534322f5 (x : Fin n → K) : x ∈ (stdH K n).L ↔ ∃ c : V → 𝓞 K,
    jB σ b x = ∑ v ∈ genB b, σ ((c v : 𝓞 K) : K) • v := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«jB_lat» := P2M_Formalism_BasicNotions_Examples__NZ_jB_lat_9c43534322f5
