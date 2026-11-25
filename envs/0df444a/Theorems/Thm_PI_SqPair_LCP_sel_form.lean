-- Prove2me | Theorems.Thm_PI_SqPair_LCP_sel_form
-- name    : PI.SqPair.LCP.sel_form
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:23:27.585231+00:00
-- url     : https://prove2.me/theorems/2bea8942-ab51-5456-9754-eac3d2022f86
-- title:
--   LCP: sel form
-- statement:
--   The LCP construction uses the sel form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SelCore.lean#L132-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SelCore.lean#L132-L139

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SelCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [IsDomain R]

theorem PI.SqPair.LCP.sel_form (σ : R ≃+* R) {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι R) (M : Matrix ι κ R) (v w : κ → R) :
    (fun l => σ ((M *ᵥ v) l)) ⬝ᵥ (A *ᵥ (M *ᵥ w)) =
      (fun l => σ (v l)) ⬝ᵥ (((M.map σ)ᵀ * A * M) *ᵥ w) := by sorry
