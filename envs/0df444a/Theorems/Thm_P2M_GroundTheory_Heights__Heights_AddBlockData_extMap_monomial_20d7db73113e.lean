-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_monomial_20d7db73113e
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_monomial_20d7db73113e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:35.34399+00:00
-- url     : https://prove2.me/theorems/1a67ac95-2c0a-460d-b632-c53bf1f4cffd
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Data ext Map monomial 20d7db73113e: P2 M Ground Theory Heights  Heights Add Block Data ext Map monomial 20d7db73113e
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Data ext Map monomial 20d7db73113e construction uses the P2 M Ground Theory Heights  Heights Add Block Data ext Map monomial 20d7db73113e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightEqMapDomain.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightEqMapDomain.lean#L28-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_WeightEqMapDomain
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
open GroundTheory.Heights₂.Heights.AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_monomial_20d7db73113e (s : Coord D.extSizes →₀ ℕ) (a : ℤ) :
    D.extMap (monomial s a) =
      monomial (s.mapDomain Sigma.fst) ((a : P.FunField) * s.prod fun v e ↦ D.extVal v ^ e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockData».«extMap_monomial» := P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_monomial_20d7db73113e
