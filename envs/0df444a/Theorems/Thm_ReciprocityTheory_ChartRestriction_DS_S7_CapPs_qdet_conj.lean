-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapPs_qdet_conj
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CapPs.qdet_conj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:09:37.104249+00:00
-- url     : https://prove2.me/theorems/a25d1d84-b0d6-5ade-93c2-eef895d1e596
-- title:
--   Cap Ps: qdet conj
-- statement:
--   The Cap Ps construction uses the qdet conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ChainHSlice.lean#L132-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ChainHSlice.lean#L132-L144

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CapPs
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
local notation "𝕄" => Matrix (Fin n) (Fin n) ℂ
local notation "𝕋" => Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ} [CompactSpace (KG ε)]

theorem ReciprocityTheory.ChartRestriction.DS.S7.CapPs.qdet_conj (A B : 𝕄) (hAB : A * B = 1) (hBA : B * A = 1) (u : ℂ) (F : 𝕄 → ℂ) (z : 𝕄) :
    Formalism.QuantumDeterminants.qdetOp negL u (fun y => F (A * y * B)) z =
      Formalism.QuantumDeterminants.qdetOp (fun a b (G : 𝕄 → ℂ) => fun w => -Lhol (A * Matrix.single a b 1 * B) G w) u F
        (A * z * B) := by sorry
