-- Prove2me | Theorems.Thm_PI_Dv_TIW_idx_le_nat
-- name    : PI.Dv.TIW.idx_le_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:18.432691+00:00
-- url     : https://prove2.me/theorems/3f70f5bf-f6dc-4d40-8625-1867ab4c9f00
-- title:
--   TIW: idx le nat
-- statement:
--   The TIW construction uses the idx le nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxNonnegOfLe.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxNonnegOfLe.lean#L37-L41

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

theorem PI.Dv.TIW.idx_le_nat (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V)) (n : ℕ) (hn : 0 < n)
    (hle : N ≤ M) (hsm : ∀ x ∈ M, ((n : ℕ) : 𝓞 K) • x ∈ N) :
    idxAt w M N ≤ (Formalism.HN.rkK M : ℤ) * vAdd w ((n : ℕ) : K) := by sorry
