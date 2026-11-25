-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionComponents_exists_ringKrullDim_quotient_eq_187ebdf244d9
-- name    : P2M_GroundTheory_Heights__Heights_SectionComponents_exists_ringKrullDim_quotient_eq_187ebdf244d9
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:17:38.969309+00:00
-- url     : https://prove2.me/theorems/dee3a219-6aef-555d-a67b-3ebf6a262a6d
-- title:
--   P2 M Ground Theory Heights  Heights Section Components exists ring Krull Dim quotient eq 187ebdf244d9: P2 M Ground Theory Heights  Heights Section Components exists ring Krull Dim quotient eq 187ebdf2
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Components exists ring Krull Dim quotient eq 187ebdf244d9 construction uses the P2 M Ground Theory Heights  Heights Section Components exists ring Krull Dim quotient eq 187ebdf244d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionComponents.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionComponents.lean#L14-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionComponents
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.SectionComponents
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SectionComponents_exists_ringKrullDim_quotient_eq_187ebdf244d9 (Q : Ideal (MvPolynomial (Fin n) F)) [Q.IsPrime] :
    ∃ m : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionComponents».«exists_ringKrullDim_quotient_eq» := P2M_GroundTheory_Heights__Heights_SectionComponents_exists_ringKrullDim_quotient_eq_187ebdf244d9
