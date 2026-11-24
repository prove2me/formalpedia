-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_reIx_smul
-- name    : PositivityTheory.Rg.Cz.CtrX.reIx_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:13.369899+00:00
-- url     : https://prove2.me/theorems/4ab673c1-343a-4336-80e6-b144fda9ad8b
-- title:
--   Ctr X: re Ix smul
-- statement:
--   The Ctr X construction uses the re Ix smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractA.lean#L30-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractA.lean#L30-L30

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

theorem PositivityTheory.Rg.Cz.CtrX.reIx_smul {P Q : Type} (e : P ≃ Q) (c : ℂ) (ξ : TV n M P) : reIx e (c • ξ) = c • reIx e ξ := by sorry
