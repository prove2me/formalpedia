-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_Aop_apply
-- name    : PositivityTheory.Rg.Cz.TGK.Aop_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:37.046858+00:00
-- url     : https://prove2.me/theorems/ecb4018d-448a-4393-8b29-1acd510272e6
-- title:
--   TGK: Aop apply
-- statement:
--   The TGK construction uses the Aop apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L17-L19

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

theorem PositivityTheory.Rg.Cz.TGK.Aop_apply (K : P → Matrix (Fin n) (Fin n) ℂ) (f : TV n M P) (I : P → Fin n) :
    Aop K f I = ∑ J, (∏ q, K q (I q) (J q)) • f J := by sorry
