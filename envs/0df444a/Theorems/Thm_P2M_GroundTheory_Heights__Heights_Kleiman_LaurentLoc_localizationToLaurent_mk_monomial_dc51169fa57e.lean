-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_monomial_dc51169fa57e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_monomial_dc51169fa57e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:52.920677+00:00
-- url     : https://prove2.me/theorems/f9cfbb6a-a864-49b8-8315-68f900ba9c47
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc localization To Laurent mk monomial dc51169fa57e: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc localization To Laurent mk monomial dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc localization To Laurent mk monomial dc51169fa57e construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc localization To Laurent mk monomial dc51169fa57e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L167-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L167-L172

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_monomial_dc51169fa57e (I : Finset (Fin (N + 1))) (p : Poly S N) (s : monos (S := S) I)
    (f : Fin (N + 1) →₀ ℕ) (hf : (s : Poly S N) = monomial f 1) :
    iotaP I (LocalizedModule.mk p s) = AddMonoidAlgebra.single (-expToInt N f) 1 * toL S N p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«localizationToLaurent_mk_monomial» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_monomial_dc51169fa57e
