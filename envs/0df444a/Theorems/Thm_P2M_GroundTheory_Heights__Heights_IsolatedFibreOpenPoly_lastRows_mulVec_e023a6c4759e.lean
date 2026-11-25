-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_lastRows_mulVec_e023a6c4759e
-- name    : P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_lastRows_mulVec_e023a6c4759e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:45:41.323154+00:00
-- url     : https://prove2.me/theorems/cc308922-4ba3-432a-a5cb-0ff13e8eec69
-- title:
--   P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly last Rows mul Vec e023a6c4759e: P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly last Rows mul Vec e023a6c4759e
-- statement:
--   The P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly last Rows mul Vec e023a6c4759e construction uses the P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly last Rows mul Vec e023a6c4759e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L33-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenPoly
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
open MvPolynomial Topology Filter Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_lastRows_mulVec_e023a6c4759e (z : Fin (n + d) → ℂ) : lastRows n d *ᵥ z = fun i => z (Fin.natAdd n i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsolatedFibreOpenPoly».«lastRows_mulVec» := P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_lastRows_mulVec_e023a6c4759e
