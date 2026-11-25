-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Swap_of_cycles_283a42f1e3cf
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Swap_of_cycles_283a42f1e3cf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:18.823165+00:00
-- url     : https://prove2.me/theorems/95f9feef-72c9-4f42-b0bf-f655e309ca0c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Swap of cycles 283a42f1e3cf: P2 M Ground Theory Heights  Heights Inter Swap of cycles 283a42f1e3cf
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Swap of cycles 283a42f1e3cf construction uses the P2 M Ground Theory Heights  Heights Inter Swap of cycles 283a42f1e3cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L177-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L177-L281

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_Swap_of_cycles_283a42f1e3cf (hCut : GeoNumCut.Statement) (hPL2 : SectionSpaceSymmetry)
    (hCyc : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
      (A A' : HermLine ι) (s s' : MRing ι), IsArithVar P (n + 2) → IsSectionOn P A s →
      IsSectionOn P A' s' → (∀ W, W ∈ divSupp P s → W ∉ divSupp P s') →
      ((divCycle P s).sum fun W m => m • divCycle W s') = (divCycle P s').sum fun W m => m • divCycle W s) :
    Swap.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Swap».«of_cycles» := P2M_GroundTheory_Heights__Heights_Inter_Swap_of_cycles_283a42f1e3cf
