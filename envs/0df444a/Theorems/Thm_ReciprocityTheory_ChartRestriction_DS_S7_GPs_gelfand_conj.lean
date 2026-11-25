-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_gelfand_conj
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.GPs.gelfand_conj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:51:37.389866+00:00
-- url     : https://prove2.me/theorems/c2445224-8af3-5efa-b2d0-5bce022010f7
-- title:
--   GPs: gelfand conj
-- statement:
--   The GPs construction uses the gelfand conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsA.lean#L233-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsA.lean#L233-L251

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ReciprocityTheory.ChartRestriction.DS.S7.GPs.gelfand_conj {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V)
    (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ a b, A * M a b * B = ∑ c, ∑ d, (P a c * Q d b) • M c d) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : ContDiffOn ℂ ∞ f V) (m : ℕ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : A * z * B ∈ V) :
    opGelfand (fun a b => Lhol (M a b)) m (fun y => f (A * y * B)) z =
      opGelfand (fun a b => Lhol (M a b)) m f (A * z * B) := by sorry
