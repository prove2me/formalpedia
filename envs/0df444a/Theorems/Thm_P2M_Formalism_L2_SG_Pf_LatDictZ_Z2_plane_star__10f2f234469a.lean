-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_star__10f2f234469a
-- name    : P2M_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_star__10f2f234469a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:45.562801+00:00
-- url     : https://prove2.me/theorems/a9ad2dd7-9b97-4553-ae20-4483d1e24d9c
-- title:
--   P2 M Formalism L2 SG Pf Lat Dict Z Z2 plane star  10f2f234469a: P2 M Formalism L2 SG Pf Lat Dict Z Z2 plane star  10f2f234469a
-- statement:
--   The P2 M Formalism L2 SG Pf Lat Dict Z Z2 plane star  10f2f234469a construction uses the P2 M Formalism L2 SG Pf Lat Dict Z Z2 plane star  10f2f234469a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L268-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L268-L273

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

theorem P2M_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_star__10f2f234469a {p : Ideal (𝓞 K)} {a : K} (h : InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) a) :
    InI p p (star a) := by sorry

alias «Formalism».«L2».«SG».«Pf».«LatDictZ».«Z2».«plane_star₂» := P2M_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_star__10f2f234469a
