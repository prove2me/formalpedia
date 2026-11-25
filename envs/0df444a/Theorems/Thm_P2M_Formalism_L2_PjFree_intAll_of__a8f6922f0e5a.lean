-- Prove2me | Theorems.Thm_P2M_Formalism_L2_PjFree_intAll_of__a8f6922f0e5a
-- name    : P2M_Formalism_L2_PjFree_intAll_of__a8f6922f0e5a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:05:52.651432+00:00
-- url     : https://prove2.me/theorems/4eb1253d-e701-5976-8d03-8f397a9d6884
-- title:
--   P2 M Formalism L2 Pj Free int All of  a8f6922f0e5a: P2 M Formalism L2 Pj Free int All of  a8f6922f0e5a
-- statement:
--   The P2 M Formalism L2 Pj Free int All of  a8f6922f0e5a construction uses the P2 M Formalism L2 Pj Free int All of  a8f6922f0e5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntAllProofFree.lean#L290-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntAllProofFree.lean#L290-L292

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
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}

theorem P2M_Formalism_L2_PjFree_intAll_of__a8f6922f0e5a (hE : IntFrExt Xo c) (hB : FrBaseChg Xo c) (hT : TanLin Xo) (hR : IntRebase Xo c) :
    IntAll Xo c := by sorry

alias «Formalism».«L2».«PjFree».«intAll_of'» := P2M_Formalism_L2_PjFree_intAll_of__a8f6922f0e5a
