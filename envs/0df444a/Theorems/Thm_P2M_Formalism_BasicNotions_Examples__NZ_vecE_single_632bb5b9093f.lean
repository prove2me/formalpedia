-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_vecE_single_632bb5b9093f
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_vecE_single_632bb5b9093f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:41.217529+00:00
-- url     : https://prove2.me/theorems/cf3f0eb9-7c75-44c3-bd79-10917ffc883c
-- title:
--   P2 M Formalism Basic Notions Examples  NZ vec E single 632bb5b9093f: P2 M Formalism Basic Notions Examples  NZ vec E single 632bb5b9093f
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ vec E single 632bb5b9093f construction uses the P2 M Formalism Basic Notions Examples  NZ vec E single 632bb5b9093f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/BasisOfBasisF.lean#L44-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/BasisOfBasisF.lean#L44-L59

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_BasisOfBasisF
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
open scoped TensorProduct nonZeroDivisors
variable (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  [Algebra.IsIntegral A B]
variable (ι : Type) [Fintype ι] [DecidableEq ι]

theorem P2M_Formalism_BasicNotions_Examples__NZ_vecE_single_632bb5b9093f (hinj : Function.Injective (algebraMap A B)) (a : ι) :
    vecE A B ι hinj (Pi.single a 1) = (1 : B) ⊗ₜ[A] (Pi.single a 1 : ι → FractionRing A) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«vecE_single» := P2M_Formalism_BasicNotions_Examples__NZ_vecE_single_632bb5b9093f
