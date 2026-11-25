-- Prove2me | Theorems.Thm_Research_arbitrarily_large_global_shell_six_counterexamples_ordinary
-- name    : Research.arbitrarily_large_global_shell_six_counterexamples_ordinary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:12:15.624688+00:00
-- url     : https://prove2.me/theorems/463c76bd-2d0b-4618-98c3-4d534bc8dd27
-- title:
--   Research: arbitrarily large global shell six counterexamples ordinary
-- statement:
--   Arbitrarily large counterexamples, now stated entirely with ordinary
--   distance at most six.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L841-L854
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L841-L854

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.arbitrarily_large_global_shell_six_counterexamples_ordinary (N : ℕ) :
    N ≤ Fintype.card (Fin (N + 1) × (Fin 365 × Fin 365)) ∧
    OrdinaryOneSeparatedOn (obliqueBlocks (N + 1)) ∧
    triCoordsWithinThirtySix.card = 126 ∧
    126 * Fintype.card (Fin (N + 1) × (Fin 365 × Fin 365)) <
      (radiusSixOrdinaryDirectedPairs (obliqueBlocks (N + 1))).card ∧
    63 * Fintype.card (Fin (N + 1) × (Fin 365 × Fin 365)) <
      (radiusSixOrdinaryOrderedPairs (obliqueBlocks (N + 1))).card := by sorry
