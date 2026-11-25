-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_bnd
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.bnd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:34.493248+00:00
-- url     : https://prove2.me/theorems/6eef90a5-859c-5fd1-ad2c-f87bcf075f1a
-- title:
--   Base0: bnd
-- statement:
--   The Base0 construction uses the bnd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/NormFixedUnitaryEntryLeOne.lean#L235-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/NormFixedUnitaryEntryLeOne.lean#L235-L339

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HalfLeNormOneSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.bnd (hk : 1 ≤ k) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) {s : ℝ} (hs : 0 ≤ s)
    {lam : ℝ} (hlam : 0 < lam) (v : Fin (2 * 0 + k + 1) → ℂ) (b : ℂ) (hb : b ≠ 0)
    (hvb : tW (iK k) v ^ 2 ≤ Complex.normSq b) :
    ∫⁻ x, ENNReal.ofReal (lam * ‖((Matrix.of x)ᴴ *ᵥ v) (iW k) + b‖) ^ (-s) ∂ν ≤
      ENNReal.ofReal (lam * ‖b‖ / 2) ^ (-s) * (C0 k s ν + ν Set.univ) := by sorry
