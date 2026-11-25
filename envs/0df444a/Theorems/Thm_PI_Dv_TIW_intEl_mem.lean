-- Prove2me | Theorems.Thm_PI_Dv_TIW_intEl_mem
-- name    : PI.Dv.TIW.intEl_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:33:02.27121+00:00
-- url     : https://prove2.me/theorems/7e47323f-a5cc-5b6c-b594-32d20c5f58ed
-- title:
--   TIW: int El mem
-- statement:
--   The TIW construction uses the int El mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/DvTransferIdxOf.lean#L85-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/DvTransferIdxOf.lean#L85-L93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.TIW.intEl_mem (ρ : Representation K G V) (L : Submodule (𝓞 K) V) (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L)
    (z : MonoidAlgebra K G) (hz : IntEl z) : ∀ x ∈ L, ρ.asAlgebraHom z x ∈ L := by sorry
