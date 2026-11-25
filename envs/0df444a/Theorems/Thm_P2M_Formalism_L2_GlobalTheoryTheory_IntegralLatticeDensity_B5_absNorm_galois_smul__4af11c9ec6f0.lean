-- Prove2me | Theorems.Thm_P2M_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_absNorm_galois_smul__4af11c9ec6f0
-- name    : P2M_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_absNorm_galois_smul__4af11c9ec6f0
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:39.236729+00:00
-- url     : https://prove2.me/theorems/b8c87bb5-aaac-4cdf-9bb4-bb764c8cdc25
-- title:
--   P2 M Formalism L2 Global Theory Theory Integral Lattice Density B5 abs Norm galois smul  4af11c9ec6f0: P2 M Formalism L2 Global Theory Theory Integral Lattice Density B5 abs Norm galois smul  4af11c9e
-- statement:
--   The P2 M Formalism L2 Global Theory Theory Integral Lattice Density B5 abs Norm galois smul  4af11c9ec6f0 construction uses the P2 M Formalism L2 Global Theory Theory Integral Lattice Density B5 abs Norm galois smul  4af11c9ec6f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/AbsNormInvMulDifferent.lean#L8-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/AbsNormInvMulDifferent.lean#L8-L13

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_AbsNormInvMulDifferent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise

theorem P2M_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_absNorm_galois_smul__4af11c9ec6f0 (E : Type) [Field E] [NumberField E] (c : E ≃ₐ[ℚ] E) (𝔟 : Ideal (𝓞 E)) :
    Ideal.absNorm (c • 𝔟) = Ideal.absNorm 𝔟 := by sorry

alias «Formalism».«L2».«GlobalTheoryTheory».«IntegralLatticeDensity».«B5».«absNorm_galois_smul'» := P2M_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_absNorm_galois_smul__4af11c9ec6f0
