-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_PrimeFiltration_equiv_055a468f012b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_PrimeFiltration_equiv_055a468f012b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:48.243187+00:00
-- url     : https://prove2.me/theorems/f3a68012-5abb-4b82-aa00-179b1372c140
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq Prime Filtration equiv 055a468f012b: P2 M Ground Theory Heights  Heights Kleiman Translate Eq Prime Filtration equiv 055a468f012b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq Prime Filtration equiv 055a468f012b construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq Prime Filtration equiv 055a468f012b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L447-L451
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L447-L451

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
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
variable (S : Type) [CommRing S] (N : ℕ)
variable {M : Type} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_PrimeFiltration_equiv_055a468f012b (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (F : IndefiniteRowSideFullHecke.Kleiman.PrimeFiltration S N G) :
    (primeFiltEquiv S N G F).n = F.n ∧ HEq (primeFiltEquiv S N G F).step F.step ∧
      HEq (primeFiltEquiv S N G F).gen F.gen ∧ HEq (primeFiltEquiv S N G F).deg F.deg ∧
      HEq (primeFiltEquiv S N G F).prime F.prime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«PrimeFiltration».«equiv» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_PrimeFiltration_equiv_055a468f012b
