-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Pj_Crude_cro_ordGe_zero__ecad83ed03f0
-- name    : P2M_Formalism_L2_Pj_Crude_cro_ordGe_zero__ecad83ed03f0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:57:29.981476+00:00
-- url     : https://prove2.me/theorems/804c80cf-95b7-4306-8b7c-d28d91ee8655
-- title:
--   P2 M Formalism L2 Pj Crude cro ord Ge zero  ecad83ed03f0: P2 M Formalism L2 Pj Crude cro ord Ge zero  ecad83ed03f0
-- statement:
--   The P2 M Formalism L2 Pj Crude cro ord Ge zero  ecad83ed03f0 construction uses the P2 M Formalism L2 Pj Crude cro ord Ge zero  ecad83ed03f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L61-L63

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}

theorem P2M_Formalism_L2_Pj_Crude_cro_ordGe_zero__ecad83ed03f0 (t : ℕ) : OrdGe t (0 : PS k n d) := by sorry

alias «Formalism».«L2».«Pj».«Crude».«cro_ordGe_zero'» := P2M_Formalism_L2_Pj_Crude_cro_ordGe_zero__ecad83ed03f0
