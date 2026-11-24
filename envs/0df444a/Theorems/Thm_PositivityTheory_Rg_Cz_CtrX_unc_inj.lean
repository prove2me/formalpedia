-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_unc_inj
-- name    : PositivityTheory.Rg.Cz.CtrX.unc_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:23.056707+00:00
-- url     : https://prove2.me/theorems/5454e14a-8724-45e5-88dc-c08b4fcc0568
-- title:
--   Ctr X: unc inj
-- statement:
--   The Ctr X construction uses the unc inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractA.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractA.lean#L23-L26

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.CtrX.unc_inj {A B : Type} {f g : TV n (TV n M A) B} (h : unc f = unc g) : f = g := by sorry
