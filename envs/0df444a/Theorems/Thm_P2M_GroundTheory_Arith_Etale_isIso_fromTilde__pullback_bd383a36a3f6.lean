-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_Etale_isIso_fromTilde__pullback_bd383a36a3f6
-- name    : P2M_GroundTheory_Arith_Etale_isIso_fromTilde__pullback_bd383a36a3f6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:31:35.052348+00:00
-- url     : https://prove2.me/theorems/c8fa5d4b-8126-429c-b7bb-44c9a51294d0
-- title:
--   P2 M Ground Theory Arith Etale is Iso from Tilde  pullback bd383a36a3f6: P2 M Ground Theory Arith Etale is Iso from Tilde  pullback bd383a36a3f6
-- statement:
--   The P2 M Ground Theory Arith Etale is Iso from Tilde  pullback bd383a36a3f6 construction uses the P2 M Ground Theory Arith Etale is Iso from Tilde  pullback bd383a36a3f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L125-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L125-L130

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u

theorem P2M_GroundTheory_Arith_Etale_isIso_fromTilde__pullback_bd383a36a3f6 {A R : CommRingCat.{u}} (φ : A ⟶ R) (N : (Spec A).Modules)
    [IsIso N.fromTildeΓ] :
    IsIso ((Scheme.Modules.pullback (Spec.map φ)).obj N).fromTildeΓ := by sorry

alias «GroundTheory».«Arith».«Etale».«isIso_fromTildeΓ_pullback» := P2M_GroundTheory_Arith_Etale_isIso_fromTilde__pullback_bd383a36a3f6
