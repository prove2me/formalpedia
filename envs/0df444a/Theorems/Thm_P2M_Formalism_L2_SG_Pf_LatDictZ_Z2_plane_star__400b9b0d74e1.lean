-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_star__400b9b0d74e1
-- name    : P2M_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_star__400b9b0d74e1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:56.113563+00:00
-- url     : https://prove2.me/theorems/96618ed9-6e30-408b-83b6-c3671ec2ae12
-- title:
--   P2 M Formalism L2 SG Pf Lat Dict Z Z2 plane star  400b9b0d74e1: P2 M Formalism L2 SG Pf Lat Dict Z Z2 plane star  400b9b0d74e1
-- statement:
--   The P2 M Formalism L2 SG Pf Lat Dict Z Z2 plane star  400b9b0d74e1 construction uses the P2 M Formalism L2 SG Pf Lat Dict Z Z2 plane star  400b9b0d74e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L260-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L260-L266

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z2
open ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_star__400b9b0d74e1 {p : Ideal (𝓞 K)} {a : K} (h : InI p p a) :
    InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) (star a) := by sorry

alias «Formalism».«L2».«SG».«Pf».«LatDictZ».«Z2».«plane_star₁» := P2M_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_star__400b9b0d74e1
