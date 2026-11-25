-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_Cell____inj_0092c5d8b628
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_Cell____inj_0092c5d8b628
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:06.512797+00:00
-- url     : https://prove2.me/theorems/9a624196-3094-476b-bf4b-be344b7f4c1e
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Cell    inj 0092c5d8b628: P2 M Formalism Hermitian Lattices Ext L3 Cell    inj 0092c5d8b628
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Cell    inj 0092c5d8b628 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Cell    inj 0092c5d8b628 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormalise.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormalise.lean#L85-L88

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOfNormRepCountNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandG
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormalise
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}

theorem P2M_Formalism_HermitianLattices_Ext_L3_Cell____inj_0092c5d8b628 {a b : 𝓞 F} (hab : κ (ι a) = κ (ι b)) : a = b := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«Cell».«κι_inj» := P2M_Formalism_HermitianLattices_Ext_L3_Cell____inj_0092c5d8b628
