-- Prove2me | Theorems.Thm_P2M_UpperTheory_V_Alg_WPres_origin___2faba994ee10
-- name    : P2M_UpperTheory_V_Alg_WPres_origin___2faba994ee10
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:08.49035+00:00
-- url     : https://prove2.me/theorems/d06981f7-69e9-5968-b38f-47467bbdea5f
-- title:
--   P2 M Upper Theory V Alg WPres origin   2faba994ee10: P2 M Upper Theory V Alg WPres origin   2faba994ee10
-- statement:
--   The P2 M Upper Theory V Alg WPres origin   2faba994ee10 construction uses the P2 M Upper Theory V Alg WPres origin   2faba994ee10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/ResMapBijective.lean#L200-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/ResMapBijective.lean#L200-L205

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebra_ResMapBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open UpperTheory UpperTheory.V UpperTheory.V.Alg
attribute [instance] IsCO.complete IsCO.isLocalHom
attribute [instance] WPres.fin
open UpperTheory.V.Alg.WPres
variable {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)

theorem P2M_UpperTheory_V_Alg_WPres_origin___2faba994ee10 (h : W.HasOrigin) (f : MvPowerSeries W.σ O) : W.origin h (W.π f) = constantCoeff f := by sorry

alias «UpperTheory».«V».«Alg».«WPres».«origin_π» := P2M_UpperTheory_V_Alg_WPres_origin___2faba994ee10
