-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2_NO_mul_mem__c3251c59e9fe
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_D2_NO_mul_mem__c3251c59e9fe
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:42:21.680479+00:00
-- url     : https://prove2.me/theorems/3f292ec5-bbee-4741-bf91-f2751bd6873f
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 D2 NO mul mem  c3251c59e9fe: P2 M Formalism Hermitian Lattices Ext L3 D2 NO mul mem  c3251c59e9fe
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 D2 NO mul mem  c3251c59e9fe construction uses the P2 M Formalism Hermitian Lattices Ext L3 D2 NO mul mem  c3251c59e9fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulEqUnifPow.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulEqUnifPow.lean#L20-L23

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
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
open Formalism.HermitianLattices.Ext.L3.D2.NO

theorem P2M_Formalism_HermitianLattices_Ext_L3_D2_NO_mul_mem__c3251c59e9fe {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {a b : K} (ha : a ∈ pK K 𝔭 k)
    (hb : b ∈ pK K 𝔭 0) : a * b ∈ pK K 𝔭 k := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«D2».«NO».«mul_mem₀» := P2M_Formalism_HermitianLattices_Ext_L3_D2_NO_mul_mem__c3251c59e9fe
