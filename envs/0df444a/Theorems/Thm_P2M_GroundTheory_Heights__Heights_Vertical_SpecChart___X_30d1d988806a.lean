-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___X_30d1d988806a
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___X_30d1d988806a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:45.939929+00:00
-- url     : https://prove2.me/theorems/5e34e20a-cd3a-450f-94fd-5a57218547c4
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart   X 30d1d988806a: P2 M Ground Theory Heights  Heights Vertical Spec Chart   X 30d1d988806a
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart   X 30d1d988806a construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart   X 30d1d988806a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L59-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L59-L59

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___X_30d1d988806a (p : Par e n) : σ e I j (X p) = val e I j p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«σ_X» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___X_30d1d988806a
