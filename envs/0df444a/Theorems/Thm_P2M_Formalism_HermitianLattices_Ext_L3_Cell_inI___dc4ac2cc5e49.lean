-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_Cell_inI___dc4ac2cc5e49
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_Cell_inI___dc4ac2cc5e49
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:29:22.33333+00:00
-- url     : https://prove2.me/theorems/0769c7ad-7fa5-494e-9e99-dc53f65e46b3
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Cell in I   dc4ac2cc5e49: P2 M Formalism Hermitian Lattices Ext L3 Cell in I   dc4ac2cc5e49
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Cell in I   dc4ac2cc5e49 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Cell in I   dc4ac2cc5e49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CongrPIffInI.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CongrPIffInI.lean#L29-L30

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_Cell_inI___dc4ac2cc5e49 (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {n : 𝓞 F} : InI 𝔭 k (κ (ι n)) ↔ n ∈ 𝔭 ^ k := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«Cell».«inI_ι» := P2M_Formalism_HermitianLattices_Ext_L3_Cell_inI___dc4ac2cc5e49
