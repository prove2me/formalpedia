-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_X_mem_supported__ad5886e30d80
-- name    : P2M_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_X_mem_supported__ad5886e30d80
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:38.203452+00:00
-- url     : https://prove2.me/theorems/6be4ad06-96d7-4dea-ba10-9290f000ee92
-- title:
--   P2 M Formalism Main Notions Test Side Words Twisted Filtration G3 X mem supported  ad5886e30d80: P2 M Formalism Main Notions Test Side Words Twisted Filtration G3 X mem supported  ad5886e30d80
-- statement:
--   The P2 M Formalism Main Notions Test Side Words Twisted Filtration G3 X mem supported  ad5886e30d80 construction uses the P2 M Formalism Main Notions Test Side Words Twisted Filtration G3 X mem supported  ad5886e30d80 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TwistSubXMemSupported.lean#L192-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TwistedMonomialFiltration/TwistSubXMemSupported.lean#L192-L205

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
open Classical

theorem P2M_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_X_mem_supported__ad5886e30d80 {B : Type*} [CommRing B] (w : Set ι) (v : ι × Fin n) (hv : v.1 ∉ w) :
    (X v : MvPolynomial (ι × Fin n) B) ∈ supported B {x : ι × Fin n | x.1 ∉ w} := by sorry

alias «Formalism».«MainNotions».«TestSideWords».«TwistedFiltration».«G3».«X_mem_supported'» := P2M_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_X_mem_supported__ad5886e30d80
