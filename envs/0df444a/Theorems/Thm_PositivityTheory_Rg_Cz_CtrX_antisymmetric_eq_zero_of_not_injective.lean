-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_antisymmetric_eq_zero_of_not_injective
-- name    : PositivityTheory.Rg.Cz.CtrX.antisymmetric_eq_zero_of_not_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:14.32991+00:00
-- url     : https://prove2.me/theorems/c583697f-e1e3-4199-9ed2-2e299d83a88b
-- title:
--   Ctr X: antisymmetric eq zero of not injective
-- statement:
--   The Ctr X construction uses the antisymmetric eq zero of not injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractD.lean#L13-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractD.lean#L13-L36

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractD
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

theorem PositivityTheory.Rg.Cz.CtrX.antisymmetric_eq_zero_of_not_injective (f : TV n M (Fin n))
    (hf : ∀ σ : Equiv.Perm (Fin n), pm σ f = ((Equiv.Perm.sign σ : ℤ) : ℂ) • f) (J : Fin n → Fin n)
    (hJ : ¬ Function.Injective J) : f J = 0 := by sorry
