-- Prove2me | Theorems.Thm_PI_Dv_TIW_idx_pi
-- name    : PI.Dv.TIW.idx_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:01.689328+00:00
-- url     : https://prove2.me/theorems/f2a3cbf0-a72e-4be9-a27e-9206a86660d6
-- title:
--   TIW: idx pi
-- statement:
--   The TIW construction uses the idx pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxNonnegOfLe.lean#L84-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxNonnegOfLe.lean#L84-L141

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
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
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.TIW.idx_pi (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (M N : ι → Submodule (𝓞 K) V) (hM : ∀ i, (M i).FG) (hN : ∀ i, (N i).FG)
    (hsp : ∀ i, Submodule.span K (M i : Set V) = Submodule.span K (N i : Set V)) :
    idxAt w (Submodule.pi Set.univ M) (Submodule.pi Set.univ N) = ∑ i, idxAt w (M i) (N i) := by sorry
