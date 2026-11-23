-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_Elliptic____ne_zero_e23ca4e0a06a
-- name    : P2M_GroundTheory_Global_Elliptic____ne_zero_e23ca4e0a06a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:36.67654+00:00
-- url     : https://prove2.me/theorems/6c93bfb7-f6e8-4326-9722-233f16e9f31d
-- title:
--   P2 M Ground Theory Global Elliptic    ne zero e23ca4e0a06a: P2 M Ground Theory Global Elliptic    ne zero e23ca4e0a06a
-- statement:
--   The P2 M Ground Theory Global Elliptic    ne zero e23ca4e0a06a construction uses the P2 M Ground Theory Global Elliptic    ne zero e23ca4e0a06a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticResidues.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticResidues.lean#L37-L40

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped Interval Real
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
variable (L)

theorem P2M_GroundTheory_Global_Elliptic____ne_zero_e23ca4e0a06a : L.ω₁ ≠ 0 := by sorry

alias «GroundTheory».«Global».«Elliptic».«ω₁_ne_zero» := P2M_GroundTheory_Global_Elliptic____ne_zero_e23ca4e0a06a
