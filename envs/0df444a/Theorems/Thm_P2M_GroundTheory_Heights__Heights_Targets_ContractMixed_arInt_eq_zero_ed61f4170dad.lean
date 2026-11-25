-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_arInt_eq_zero_ed61f4170dad
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_arInt_eq_zero_ed61f4170dad
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:43:22.174876+00:00
-- url     : https://prove2.me/theorems/d2b7d21e-03ff-5027-b445-45c175cb4975
-- title:
--   P2 M Ground Theory Heights  Heights Targets Contract Mixed ar Int eq zero ed61f4170dad: P2 M Ground Theory Heights  Heights Targets Contract Mixed ar Int eq zero ed61f4170dad
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Contract Mixed ar Int eq zero ed61f4170dad construction uses the P2 M Ground Theory Heights  Heights Targets Contract Mixed ar Int eq zero ed61f4170dad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixed.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixed.lean#L39-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFIntZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ContractMixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Targets.ContractMixed
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_arInt_eq_zero_ed61f4170dad (hInt : PFIntZero.Statement) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d₀ n : ℕ} (hP' : IsArithVar P' (n + 1))
    (hQ : IsArithVar (imageZ v P') d₀) {L' : Fin n → HermLine ι'} (hpre : PrefixPull κ v d₀ L')
    (A : HermLine ι') (s : MRing ι') : arInt P' s A L' = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ContractMixed».«arInt_eq_zero» := P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_arInt_eq_zero_ed61f4170dad
