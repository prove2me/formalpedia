-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedCech_hEquiv_mk_ddf70a59c8c8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedCech_hEquiv_mk_ddf70a59c8c8
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:13.133802+00:00
-- url     : https://prove2.me/theorems/ec8d7883-76f9-4502-ac2f-9a4b26f5f43a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq Graded Cech h Equiv mk ddf70a59c8c8: P2 M Ground Theory Heights  Heights Kleiman Translate Eq Graded Cech h Equiv mk ddf70a59c8c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq Graded Cech h Equiv mk ddf70a59c8c8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq Graded Cech h Equiv mk ddf70a59c8c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqCech.lean#L298-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqCech.lean#L298-L299

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqCech
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech
variable (S : Type) [CommRing S] (N : ℕ)
variable (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {S N M}
variable (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedCech_hEquiv_mk_ddf70a59c8c8 (i : ℕ) (w : IndefiniteRowSideFullHecke.Kleiman.gradedZ S N M G i c) :
    hEquiv G c i (Submodule.Quotient.mk w) = Submodule.Quotient.mk (zEquiv G c i w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«GradedCech».«hEquiv_mk» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedCech_hEquiv_mk_ddf70a59c8c8
