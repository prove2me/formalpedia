-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Cz_TA_qdet_map__2871d26b2e36
-- name    : P2M_PositivityTheory_Rg_Cz_TA_qdet_map__2871d26b2e36
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:39.710847+00:00
-- url     : https://prove2.me/theorems/a2376e0b-83d4-4ec3-93ae-173ee134e3f3
-- title:
--   P2 M Positivity Theory Rg Cz TA qdet map  2871d26b2e36: P2 M Positivity Theory Rg Cz TA qdet map  2871d26b2e36
-- statement:
--   The P2 M Positivity Theory Rg Cz TA qdet map  2871d26b2e36 construction uses the P2 M Positivity Theory Rg Cz TA qdet map  2871d26b2e36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean#L11-L13

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem P2M_PositivityTheory_Rg_Cz_TA_qdet_map__2871d26b2e36 {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {m : ℕ} (φ : A →ₐ[ℂ] B)
    (E : Fin m → Fin m → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by sorry

alias «PositivityTheory».«Rg».«Cz».«TA».«qdet_map'» := P2M_PositivityTheory_Rg_Cz_TA_qdet_map__2871d26b2e36
