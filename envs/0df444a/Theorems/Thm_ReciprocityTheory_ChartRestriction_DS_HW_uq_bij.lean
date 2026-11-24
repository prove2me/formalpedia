-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_bij
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.uq_bij
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:32:55.300134+00:00
-- url     : https://prove2.me/theorems/d4ba874c-cecd-44b8-a52e-167d00476d13
-- title:
--   HW: uq bij
-- statement:
--   The HW construction uses the uq bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/UniqueA.lean#L72-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/UniqueA.lean#L72-L209

import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open Formalism.REAL
variable {n : ℕ}
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem ReciprocityTheory.ChartRestriction.DS.HW.uq_bij {P U : Type} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P]
    [AddCommGroup U] [Module ℂ U] (ε : Fin n → Bool) (G : Fin n → Fin n → Module.End ℂ P)
    (F : Fin n → Fin n → Module.End ℂ U) (μ : Fin n → ℝ) (x : P) (hR : KRel ε G) (hU : KUnit ε G)
    (hx : KHighest ε G μ x) (p : P →ₗ[ℂ] U) (hp : ∀ a b, ε a = ε b → ∀ y, p (G a b y) = F a b (p y))
    (hpx : p x ≠ 0) (hT : kSpan ε F (p x) = ⊤) : Function.Bijective (p.domRestrict (kSpan ε G x)) := by sorry
