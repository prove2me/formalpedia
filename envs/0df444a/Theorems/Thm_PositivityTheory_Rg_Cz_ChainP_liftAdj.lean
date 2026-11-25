-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_liftAdj
-- name    : PositivityTheory.Rg.Cz.ChainP.liftAdj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:48:21.760083+00:00
-- url     : https://prove2.me/theorems/d8684262-7b0e-4ced-8480-6a74bbdd6d14
-- title:
--   Chain P: lift Adj
-- statement:
--   The Chain P construction uses the lift Adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChain.lean#L101-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChain.lean#L101-L133

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChain
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.ChainP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.ChainP.liftAdj (hC : Curry) (E : Fin n → Fin n → Module.End ℂ M) (m : ℕ) :
    ∀ g ∈ Algebra.adjoin ℂ (Set.range fun j : Fin m => xJ E j), ∃ g' ∈ Algebra.adjoin ℂ
      (Set.range fun j : Fin (m + 1) => xJ E j), curF n M m 1 ∘ₗ g' =
        (lift g : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1))) ∘ₗ curF n M m 1 := by sorry
