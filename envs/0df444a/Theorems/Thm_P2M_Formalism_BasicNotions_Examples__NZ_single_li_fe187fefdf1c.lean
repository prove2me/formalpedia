-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_single_li_fe187fefdf1c
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_single_li_fe187fefdf1c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:52:59.071797+00:00
-- url     : https://prove2.me/theorems/cf6ef81d-396f-4a14-b34e-c278f3e3db95
-- title:
--   P2 M Formalism Basic Notions Examples  NZ single li fe187fefdf1c: P2 M Formalism Basic Notions Examples  NZ single li fe187fefdf1c
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ single li fe187fefdf1c construction uses the P2 M Formalism Basic Notions Examples  NZ single li fe187fefdf1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/BasisOfBasisF.lean#L61-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/BasisOfBasisF.lean#L61-L69

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_single_li_fe187fefdf1c (hB : Function.Injective (algebraMap B (FractionRing B))) :
    LinearIndependent B (fun a : ι => (Pi.single a 1 : ι → FractionRing B)) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«single_li» := P2M_Formalism_BasicNotions_Examples__NZ_single_li_fe187fefdf1c
