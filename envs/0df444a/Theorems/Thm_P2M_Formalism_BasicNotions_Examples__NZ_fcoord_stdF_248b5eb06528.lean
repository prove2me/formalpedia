-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_fcoord_stdF_248b5eb06528
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_fcoord_stdF_248b5eb06528
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:29.976733+00:00
-- url     : https://prove2.me/theorems/a287428b-3903-4576-bc20-9fe61f5d7537
-- title:
--   P2 M Formalism Basic Notions Examples  NZ fcoord std F 248b5eb06528: P2 M Formalism Basic Notions Examples  NZ fcoord std F 248b5eb06528
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ fcoord std F 248b5eb06528 construction uses the P2 M Formalism Basic Notions Examples  NZ fcoord std F 248b5eb06528 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L134-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L134-L137

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_fcoord_stdF_248b5eb06528 (v : InfinitePlace K) (x : Fin n → K) (i : Fin n) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v x i =
      v.embedding (x i) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«fcoord_stdF» := P2M_Formalism_BasicNotions_Examples__NZ_fcoord_stdF_248b5eb06528
