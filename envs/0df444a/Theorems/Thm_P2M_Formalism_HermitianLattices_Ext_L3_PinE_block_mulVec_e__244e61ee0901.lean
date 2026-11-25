-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_PinE_block_mulVec_e__244e61ee0901
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_PinE_block_mulVec_e__244e61ee0901
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:06.475536+00:00
-- url     : https://prove2.me/theorems/b11f38cf-2904-4651-a8a0-abe122a7a9ef
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Pin E block mul Vec e  244e61ee0901: P2 M Formalism Hermitian Lattices Ext L3 Pin E block mul Vec e  244e61ee0901
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Pin E block mul Vec e  244e61ee0901 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Pin E block mul Vec e  244e61ee0901 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EqBlockOfFix.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EqBlockOfFix.lean#L18-L23

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EqBlockOfFix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinE
variable {A : Type*} [CommRing A] [StarRing A] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem P2M_Formalism_HermitianLattices_Ext_L3_PinE_block_mulVec_e__244e61ee0901 (X' : Matrix κ κ A) :
    (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) *ᵥ e₀ = e₀ := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«PinE».«block_mulVec_e₀» := P2M_Formalism_HermitianLattices_Ext_L3_PinE_block_mulVec_e__244e61ee0901
