-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_gal_KEd__K_77cda8eaa892
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_gal_KEd__K_77cda8eaa892
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:09:38.129049+00:00
-- url     : https://prove2.me/theorems/5acd4b7e-2e3c-5f9d-9004-7dfbc0c781e5
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 gal KEd  K 77cda8eaa892: P2 M Formalism Hermitian Lattices Ext L3 gal KEd  K 77cda8eaa892
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 gal KEd  K 77cda8eaa892 construction uses the P2 M Formalism Hermitian Lattices Ext L3 gal KEd  K 77cda8eaa892 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandD.lean#L179-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandD.lean#L179-L186

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (w : K) (hw0 : w ≠ 0) (hw : star w = -w) (d : cmF K) [Fact (Irreducible (polE d))]
  [Fact (Irreducible (polKE d (skewSq w hw)))]

theorem P2M_Formalism_HermitianLattices_Ext_L3_gal_KEd__K_77cda8eaa892 (τ : KEd d (skewSq w hw) ≃ₐ[Ed d] KEd d (skewSq w hw)) :
    (∀ x : K, τ (ιK w hw d x) = ιK w hw d x) ∨ ∀ x : K, τ (ιK w hw d x) = ιK w hw d (star x) := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«gal_KEd_ιK» := P2M_Formalism_HermitianLattices_Ext_L3_gal_KEd__K_77cda8eaa892
