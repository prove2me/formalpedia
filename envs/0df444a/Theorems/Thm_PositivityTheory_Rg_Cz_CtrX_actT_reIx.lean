-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_actT_reIx
-- name    : PositivityTheory.Rg.Cz.CtrX.actT_reIx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:46.513108+00:00
-- url     : https://prove2.me/theorems/469bdb65-d2c2-4252-b1e9-56f8cc01aa74
-- title:
--   Ctr X: act T re Ix
-- statement:
--   The Ctr X construction uses the act T re Ix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractA.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractA.lean#L32-L45

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

theorem PositivityTheory.Rg.Cz.CtrX.actT_reIx {ι Γ P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] (e : P ≃ Q)
    (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ) (ξ : TV n M P) :
    actT (lab ∘ e.symm) κ ρ γ (reIx e ξ) = reIx e (actT lab κ ρ γ ξ) := by sorry
