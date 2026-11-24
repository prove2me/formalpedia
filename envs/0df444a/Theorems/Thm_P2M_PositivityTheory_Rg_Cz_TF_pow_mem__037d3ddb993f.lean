-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Cz_TF_pow_mem__037d3ddb993f
-- name    : P2M_PositivityTheory_Rg_Cz_TF_pow_mem__037d3ddb993f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:26.215792+00:00
-- url     : https://prove2.me/theorems/03bc09f2-34c2-4537-8863-a52425bfea2d
-- title:
--   P2 M Positivity Theory Rg Cz TF pow mem  037d3ddb993f: P2 M Positivity Theory Rg Cz TF pow mem  037d3ddb993f
-- statement:
--   The P2 M Positivity Theory Rg Cz TF pow mem  037d3ddb993f construction uses the P2 M Positivity Theory Rg Cz TF pow mem  037d3ddb993f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFinCK.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFinCK.lean#L9-L14

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinCK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TF

theorem P2M_PositivityTheory_Rg_Cz_TF_pow_mem__037d3ddb993f {U : Type*} [AddCommGroup U] [Module ℂ U] (T : Module.End ℂ U) (Z : Submodule ℂ U)
    (hZ : ∀ z ∈ Z, T z ∈ Z) : ∀ k : ℕ, ∀ z ∈ Z, (T ^ k) z ∈ Z := by sorry

alias «PositivityTheory».«Rg».«Cz».«TF».«pow_mem'» := P2M_PositivityTheory_Rg_Cz_TF_pow_mem__037d3ddb993f
