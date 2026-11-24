-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_jB_basis_3f775679a4b7
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_jB_basis_3f775679a4b7
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:59:34.28481+00:00
-- url     : https://prove2.me/theorems/248f4db0-916b-4bc5-91f2-d37588af84af
-- title:
--   P2 M Formalism Basic Notions Examples  NZ j B basis 3f775679a4b7: P2 M Formalism Basic Notions Examples  NZ j B basis 3f775679a4b7
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ j B basis 3f775679a4b7 construction uses the P2 M Formalism Basic Notions Examples  NZ j B basis 3f775679a4b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L126-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L126-L132

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_jB_basis_3f775679a4b7 : LinearIndependent ℂ (fun i => jB σ b ((stdH K n).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jB σ b ((stdH K n).b i))) = ⊤ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«jB_basis» := P2M_Formalism_BasicNotions_Examples__NZ_jB_basis_3f775679a4b7
