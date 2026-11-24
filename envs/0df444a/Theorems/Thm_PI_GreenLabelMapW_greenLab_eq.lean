-- Prove2me | Theorems.Thm_PI_GreenLabelMapW_greenLab_eq
-- name    : PI.GreenLabelMapW.greenLab_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:35.892802+00:00
-- url     : https://prove2.me/theorems/c6f09707-9395-47c5-859f-620f689c5d0d
-- title:
--   Green Label Map W: green Lab eq
-- statement:
--   The Green Label Map W construction uses the green Lab eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/IrreducibleCharpolyInv.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/IrreducibleCharpolyInv.lean#L43-L46

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem PI.GreenLabelMapW.greenLab_eq (Cv : LabelConv K) (hC : CuspParam K Cv) {d : ℕ} (hd : 1 ≤ d)
    {τ : FDRep ℂ (GL (Fin d) K)} (hs : Simple τ) (hc : IsCuspidal K τ) {P : K[X]}
    (hP : HasCuspLabel Cv τ P) : greenLab Cv d τ = P := by sorry
