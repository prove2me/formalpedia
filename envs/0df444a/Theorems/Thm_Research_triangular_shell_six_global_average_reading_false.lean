-- Prove2me | Theorems.Thm_Research_triangular_shell_six_global_average_reading_false
-- name    : Research.triangular_shell_six_global_average_reading_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:11:59.773989+00:00
-- url     : https://prove2.me/theorems/b206d284-8236-54a3-b8a1-758fe0ea54a8
-- title:
--   Research: triangular shell six global average reading false
-- statement:
--   Final shell-six resolution: the comparison value is exactly 126, but both
--   natural global normalizations fail on arbitrarily large one-separated sets.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L902-L908
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L902-L908

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.triangular_shell_six_global_average_reading_false :
    triCoordsWithinThirtySix.card = 126 ∧
      ¬ EventualShellSixDirectedAverageBound ∧
      ¬ EventualShellSixUnorderedBound := by sorry
