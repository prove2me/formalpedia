-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:43.508806+00:00
-- url     : https://prove2.me/theorems/0e57ec7b-b8bd-4e1b-b3f1-34fa25703f40
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety mk F eq zero iff 91580b64c057: P2 M Ground Theory Heights  Heights Arith Variety mk F eq zero iff 91580b64c057
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety mk F eq zero iff 91580b64c057 construction uses the P2 M Ground Theory Heights  Heights Arith Variety mk F eq zero iff 91580b64c057 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean#L77-L79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.ArithVariety
variable (P : ArithVariety n)
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057 (f : MvPolynomial (Coord n) ℤ) : P.mkF f = 0 ↔ f ∈ P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«mkF_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
