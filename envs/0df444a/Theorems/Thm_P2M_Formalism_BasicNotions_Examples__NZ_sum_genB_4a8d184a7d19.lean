-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_sum_genB_4a8d184a7d19
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_sum_genB_4a8d184a7d19
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:49:13.24995+00:00
-- url     : https://prove2.me/theorems/22432cff-b9bd-4ae3-bbcc-c8ea232535c6
-- title:
--   P2 M Formalism Basic Notions Examples  NZ sum gen B 4a8d184a7d19: P2 M Formalism Basic Notions Examples  NZ sum gen B 4a8d184a7d19
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ sum gen B 4a8d184a7d19 construction uses the P2 M Formalism Basic Notions Examples  NZ sum gen B 4a8d184a7d19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L149-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L149-L151

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_sum_genB_4a8d184a7d19 (f : V → V) : ∑ v ∈ genB b, f v = ∑ i, f (b i) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«sum_genB» := P2M_Formalism_BasicNotions_Examples__NZ_sum_genB_4a8d184a7d19
