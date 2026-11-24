-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_jB_basis0_9ad344eafbe3
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_jB_basis0_9ad344eafbe3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:47:48.257499+00:00
-- url     : https://prove2.me/theorems/2b008d00-892c-4db6-991c-a3efcfc23df7
-- title:
--   P2 M Formalism Basic Notions Examples  NZ j B basis0 9ad344eafbe3: P2 M Formalism Basic Notions Examples  NZ j B basis0 9ad344eafbe3
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ j B basis0 9ad344eafbe3 construction uses the P2 M Formalism Basic Notions Examples  NZ j B basis0 9ad344eafbe3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L88-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L88-L94

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_jB_basis0_9ad344eafbe3 : LinearIndependent ℂ (fun i => jB σ b (Pi.basisFun K (Fin n) i)) ∧
    Submodule.span ℂ (Set.range (fun i => jB σ b (Pi.basisFun K (Fin n) i))) = ⊤ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«jB_basis0» := P2M_Formalism_BasicNotions_Examples__NZ_jB_basis0_9ad344eafbe3
