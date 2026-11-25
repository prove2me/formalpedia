-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_conj_single
-- name    : PositivityTheory.Rg.Cz.TGK.conj_single
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:58.172836+00:00
-- url     : https://prove2.me/theorems/bb653f0d-af54-50ac-8708-81f216e484b9
-- title:
--   TGK: conj single
-- statement:
--   The TGK construction uses the conj single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L183-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L183-L187

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TGK.conj_single (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ∑ c, ∑ d, (U c a * star (U d b)) • Matrix.single c d (1 : ℂ) = U * Matrix.single a b 1 * Uᴴ := by sorry
