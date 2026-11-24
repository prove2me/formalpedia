-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_ht_cons
-- name    : PositivityTheory.Rg.Cz.HeightVanishing.ht_cons
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:53.709654+00:00
-- url     : https://prove2.me/theorems/a66bd744-2db4-4074-9e5e-1a67107beef5
-- title:
--   Height Vanishing: ht cons
-- statement:
--   The Height Vanishing construction uses the ht cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L23-L25

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
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
open PositivityTheory.Rg.Cz.HeightVanishing
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable (E : Fin n → Fin n → Module.End ℂ M)

theorem PositivityTheory.Rg.Cz.HeightVanishing.ht_cons (x : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    ht (x :: w) = (((x.2 : ℕ) : ℤ) - ((x.1 : ℕ) : ℤ)) + ht w := by sorry
