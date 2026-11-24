-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___C_90452924d03a
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___C_90452924d03a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:07.287281+00:00
-- url     : https://prove2.me/theorems/f0781ae3-d528-4bcc-940b-eb050151f9d1
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart   C 90452924d03a: P2 M Ground Theory Heights  Heights Vertical Spec Chart   C 90452924d03a
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart   C 90452924d03a construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart   C 90452924d03a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L61-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L61-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___C_90452924d03a (c : 𝓞 K) : σ e I j (C c) = C (toBase I j (C c)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«σ_C» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___C_90452924d03a
