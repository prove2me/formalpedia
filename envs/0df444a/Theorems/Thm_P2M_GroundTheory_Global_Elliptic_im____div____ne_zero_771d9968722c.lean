-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_Elliptic_im____div____ne_zero_771d9968722c
-- name    : P2M_GroundTheory_Global_Elliptic_im____div____ne_zero_771d9968722c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:18.247099+00:00
-- url     : https://prove2.me/theorems/87459530-faf8-4384-9a35-cf56e6dc0e9e
-- title:
--   P2 M Ground Theory Global Elliptic im    div    ne zero 771d9968722c: P2 M Ground Theory Global Elliptic im    div    ne zero 771d9968722c
-- statement:
--   The P2 M Ground Theory Global Elliptic im    div    ne zero 771d9968722c construction uses the P2 M Ground Theory Global Elliptic im    div    ne zero 771d9968722c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticResidues.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticResidues.lean#L43-L53

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

theorem P2M_GroundTheory_Global_Elliptic_im____div____ne_zero_771d9968722c : (L.ω₂ / L.ω₁).im ≠ 0 := by sorry

alias «GroundTheory».«Global».«Elliptic».«im_ω₂_div_ω₁_ne_zero» := P2M_GroundTheory_Global_Elliptic_im____div____ne_zero_771d9968722c
