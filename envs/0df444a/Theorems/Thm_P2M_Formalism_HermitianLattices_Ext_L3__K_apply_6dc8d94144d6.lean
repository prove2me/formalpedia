-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3__K_apply_6dc8d94144d6
-- name    : P2M_Formalism_HermitianLattices_Ext_L3__K_apply_6dc8d94144d6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:43.388771+00:00
-- url     : https://prove2.me/theorems/c4c004b4-886f-4013-b068-d65ddea4f27f
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3  K apply 6dc8d94144d6: P2 M Formalism Hermitian Lattices Ext L3  K apply 6dc8d94144d6
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3  K apply 6dc8d94144d6 construction uses the P2 M Formalism Hermitian Lattices Ext L3  K apply 6dc8d94144d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandD.lean#L164-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandD.lean#L164-L166

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

theorem P2M_Formalism_HermitianLattices_Ext_L3__K_apply_6dc8d94144d6 (x : K) : ιK w hw d x = algebraMap (cmF K) (KEd d (skewSq w hw)) (reF x) +
    algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw x) *
      AdjoinRoot.root (polKE d (skewSq w hw)) := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«ιK_apply» := P2M_Formalism_HermitianLattices_Ext_L3__K_apply_6dc8d94144d6
