-- Prove2me | Theorems.Thm_Research_arbitrarily_large_global_shell_six_counterexamples
-- name    : Research.arbitrarily_large_global_shell_six_counterexamples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:02:42.515096+00:00
-- url     : https://prove2.me/theorems/68236cfc-d145-479a-8189-50adef74bd33
-- title:
--   Research: arbitrarily large global shell six counterexamples
-- statement:
--   Source-facing arbitrary-size counterexamples: above every requested
--   cardinality there is a one-separated finite configuration violating both the
--   directed average-degree and direct unordered shell-six bounds.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L811-L825
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L811-L825

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.arbitrarily_large_global_shell_six_counterexamples (N : ℕ) :
    N ≤ Fintype.card (Fin (N + 1) × (Fin 365 × Fin 365)) ∧
    (∀ q s : Fin (N + 1) × (Fin 365 × Fin 365), q ≠ s →
      1 ≤ sqDist (obliqueBlocks (N + 1) q) (obliqueBlocks (N + 1) s)) ∧
    triCoordsWithinThirtySix.card = 126 ∧
    126 * Fintype.card (Fin (N + 1) × (Fin 365 × Fin 365)) <
      (radiusSixDirectedPairs (obliqueBlocks (N + 1))).card ∧
    63 * Fintype.card (Fin (N + 1) × (Fin 365 × Fin 365)) <
      (radiusSixOrderedPairs (obliqueBlocks (N + 1))).card := by sorry
