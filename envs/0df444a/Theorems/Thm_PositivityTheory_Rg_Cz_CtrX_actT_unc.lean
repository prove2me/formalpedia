-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_actT_unc
-- name    : PositivityTheory.Rg.Cz.CtrX.actT_unc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:27.377261+00:00
-- url     : https://prove2.me/theorems/6e3d4077-4708-4d77-b287-ae7243f49f48
-- title:
--   Ctr X: act T unc
-- statement:
--   The Ctr X construction uses the act T unc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractA.lean#L47-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractA.lean#L47-L57

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

theorem PositivityTheory.Rg.Cz.CtrX.actT_unc {ι Γ A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (la : A → ι) (lb : B → ι)
    (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ) (f : TV n (TV n M A) B) :
    actT (Sum.elim la lb) κ ρ γ (unc f) = unc (actT lb κ (actT la κ ρ) γ f) := by sorry
