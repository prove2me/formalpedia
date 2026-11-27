-- Prove2me | Theorems.Thm_P2M_Formalism_L2_PjFree_intFrNe_of__7f5ea7e93907
-- name    : P2M_Formalism_L2_PjFree_intFrNe_of__7f5ea7e93907
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:07.11251+00:00
-- url     : https://prove2.me/theorems/bab4aa71-2958-4ec7-8e10-3e5a4254e867
-- title:
--   P2 M Formalism L2 Pj Free int Fr Ne of  7f5ea7e93907: P2 M Formalism L2 Pj Free int Fr Ne of  7f5ea7e93907
-- statement:
--   The P2 M Formalism L2 Pj Free int Fr Ne of  7f5ea7e93907 construction uses the P2 M Formalism L2 Pj Free int Fr Ne of  7f5ea7e93907 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntAllProofFree.lean#L115-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntAllProofFree.lean#L115-L126

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem P2M_Formalism_L2_PjFree_intFrNe_of__7f5ea7e93907 (hN : XoNumPt Xo c) (hL : LocFld) (hE : IntFrExt Xo c) : IntFrNe Xo c (algCls Xo c) := by sorry

alias «Formalism».«L2».«PjFree».«intFrNe_of'» := P2M_Formalism_L2_PjFree_intFrNe_of__7f5ea7e93907
