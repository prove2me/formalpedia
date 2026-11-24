-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2___pow_smul_cc25b347fe94
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_D2___pow_smul_cc25b347fe94
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:46:12.505819+00:00
-- url     : https://prove2.me/theorems/0d28a754-a599-4302-9edd-0adb7b96bbda
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 D2   pow smul cc25b347fe94: P2 M Formalism Hermitian Lattices Ext L3 D2   pow smul cc25b347fe94
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 D2   pow smul cc25b347fe94 construction uses the P2 M Formalism Hermitian Lattices Ext L3 D2   pow smul cc25b347fe94 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsEquivOfMemEndL.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsEquivOfMemEndL.lean#L16-L21

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsEquivOfMemEndL
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem P2M_Formalism_HermitianLattices_Ext_L3_D2___pow_smul_cc25b347fe94 (π : 𝓞 F) (r : ℕ) (w : V) :
    ι (π ^ r) • w = algebraMap F K (π : F) ^ r • w := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«D2».«ι_pow_smul» := P2M_Formalism_HermitianLattices_Ext_L3_D2___pow_smul_cc25b347fe94
