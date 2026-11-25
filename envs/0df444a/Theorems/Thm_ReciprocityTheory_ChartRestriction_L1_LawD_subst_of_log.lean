-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_subst_of_log
-- name    : ReciprocityTheory.ChartRestriction.L1.LawD.subst_of_log
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:39.791802+00:00
-- url     : https://prove2.me/theorems/6b04887e-94fc-44a0-af24-297d04dd87a1
-- title:
--   Law D: subst of log
-- statement:
--   The Law D construction uses the subst of log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/SubstOfLog.lean#L15-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/SubstOfLog.lean#L15-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_DivByPartialYAtZeroSubstAtXAtY
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SubstOfLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem ReciprocityTheory.ChartRestriction.L1.LawD.subst_of_log (h : LawD lam Φ) {e : PowerSeries K} {c : K} (he0 : constantCoeff e = 0)
    (hlog : lam.subst e = C c * lam) : e.subst Φ = Φ.subst ![atX e, atY e] := by sorry
