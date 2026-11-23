-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitA_mem_dualAt_iff__473848215253
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_SplitA_mem_dualAt_iff__473848215253
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:13.011798+00:00
-- url     : https://prove2.me/theorems/0a9c6874-385c-4347-8a3f-c37e28e20025
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Split A mem dual At iff  473848215253: P2 M Formalism Hermitian Lattices Ext L3 Split A mem dual At iff  473848215253
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Split A mem dual At iff  473848215253 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Split A mem dual At iff  473848215253 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemHcompl.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemHcompl.lean#L54-L59

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitA
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_HermitianLattices_Ext_L3_SplitA_mem_dualAt_iff__473848215253 {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (g : W →ₗ⋆[K] W →ₗ[K] K) (p : Ideal (𝓞 K))
    (M : Submodule (𝓞 K) W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.dualAt g p M ↔ ∀ y ∈ M, g y x ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«SplitA».«mem_dualAt_iff'» := P2M_Formalism_HermitianLattices_Ext_L3_SplitA_mem_dualAt_iff__473848215253
