-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2_c__ne_zero_3faafbcab9f8
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_D2_c__ne_zero_3faafbcab9f8
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:36.247049+00:00
-- url     : https://prove2.me/theorems/5ca42329-c329-4faf-bf93-179d688d0cae
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 D2 c  ne zero 3faafbcab9f8: P2 M Formalism Hermitian Lattices Ext L3 D2 c  ne zero 3faafbcab9f8
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 D2 c  ne zero 3faafbcab9f8 construction uses the P2 M Formalism Hermitian Lattices Ext L3 D2 c  ne zero 3faafbcab9f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulMemPrimePower.lean#L88-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulMemPrimePower.lean#L88-L94

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
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

theorem P2M_Formalism_HermitianLattices_Ext_L3_D2_c__ne_zero_3faafbcab9f8 {x : 𝓞 F} (hx : x ≠ 0) : algebraMap (𝓞 K) K (ι x) ≠ 0 := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«D2».«cι_ne_zero» := P2M_Formalism_HermitianLattices_Ext_L3_D2_c__ne_zero_3faafbcab9f8
