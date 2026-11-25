-- Prove2me | Theorems.Thm_P2M_Formalism_BranchingDeterminantCap_PrismTransfer_pow_ne_zero__012ddc03cd71
-- name    : P2M_Formalism_BranchingDeterminantCap_PrismTransfer_pow_ne_zero__012ddc03cd71
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:54:04.115442+00:00
-- url     : https://prove2.me/theorems/34783f38-1c9d-4293-ab3d-536750e27401
-- title:
--   P2 M Formalism Branching Determinant Cap Prism Transfer pow ne zero  012ddc03cd71: P2 M Formalism Branching Determinant Cap Prism Transfer pow ne zero  012ddc03cd71
-- statement:
--   The P2 M Formalism Branching Determinant Cap Prism Transfer pow ne zero  012ddc03cd71 construction uses the P2 M Formalism Branching Determinant Cap Prism Transfer pow ne zero  012ddc03cd71 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L352-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Transfer.lean#L352-L352

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
open PrismTransfer
open Formalism.BranchingDeterminantCap.PrismTransfer
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem P2M_Formalism_BranchingDeterminantCap_PrismTransfer_pow_ne_zero__012ddc03cd71 (G : ℕ) (hG : 0 < G) : ((G : K) ^ 3) ≠ 0 := by sorry

alias «Formalism».«BranchingDeterminantCap».«PrismTransfer».«pow_ne_zero'» := P2M_Formalism_BranchingDeterminantCap_PrismTransfer_pow_ne_zero__012ddc03cd71
