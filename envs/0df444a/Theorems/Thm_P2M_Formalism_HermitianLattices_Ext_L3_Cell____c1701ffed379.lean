-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_Cell____c1701ffed379
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_Cell____c1701ffed379
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:29:03.940354+00:00
-- url     : https://prove2.me/theorems/f8718c8d-bf5e-53e6-a742-41cd24066aab
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Cell    c1701ffed379: P2 M Formalism Hermitian Lattices Ext L3 Cell    c1701ffed379
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Cell    c1701ffed379 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Cell    c1701ffed379 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CongrPIffInI.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CongrPIffInI.lean#L20-L20

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
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
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem P2M_Formalism_HermitianLattices_Ext_L3_Cell____c1701ffed379 (t : 𝓞 F) : κ (ι t) = algebraMap F K (t : F) := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«Cell».«κι» := P2M_Formalism_HermitianLattices_Ext_L3_Cell____c1701ffed379
