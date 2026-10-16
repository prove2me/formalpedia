-- Prove2me | Theorems.Thm_PersistClust_Count_t6_assemble
-- name    : PersistClust.Count.t6_assemble
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T12:08:47.067975+00:00
-- url     : https://prove2.me/theorems/c083fc73-09b3-4b0a-9f6e-b39a57c7d7bf
-- title:
--   Schroeder-Bernstein matching assembly: two injective demand-copy maps yield a copy equivalence satisfying the gate clauses I and II
-- statement:
--   Fix a level alpha and a radius eps >= 0. Let DX and DY be diagram-like persistence diagrams over the extended-real plane with finite support, with off-diagonal copies (points carrying copy indices below the multiplicity) and diagonal slots. Call an off-diagonal copy DEMANDED when the diagonal cannot absorb it at radius eps (either prominent -- strictly above alpha in both coordinates and not eps-absorbable -- or the high-far QSE bundle). Assume there are injective maps on demanded copies in BOTH directions: F from the demanded X-copies into the Y-copies, and G from the demanded Y-copies into the X-copies, such that (a) every prominent copy maps to a copy eps-close to it in BOTH coordinates, and (b) every copy whose point lies in the strict QSE quadrant maps to a copy eps-close in the birth coordinate -- and if that image lands in the strict quadrant, the closeness upgrades to both coordinates. Then there exists a bijection gamma between ALL X-copies and ALL Y-copies (diagonal slots included) that satisfies the matching gate clauses I and II: quadrant membership and eps-closeness are preserved in both directions. The proof is a Schroeder-Bernstein argument: demanded copies ride the given injections, non-demanded copies are absorbed to eps-close diagonal points, injective natural-number codes separate the sectors by parity, and Mathlib's relational Schroeder-Bernstein theorem converts the two injections into the global bijection. This is the assembly engine of the persistence-clustering interleaving matching: it upgrades one-sided Hall-type copy injections on the demanded sectors to a full matching equivalence of the copy structures. All structures (copies, diagram-likeness, quadrants, demands, closeness, the gate predicate) are the platform's Definitions.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8 cluster): the Schroeder-Bernstein assembly of the interleaving matching (injective demand-copy maps in both directions, with the prominent/QSE closeness clauses, yield a full copy equivalence satisfying the gate clauses I and II). Transcribed GREEN (exit 0, sorry-free) from the working file; the 11-declaration helper chain (copy codes and their injectivity, odd/even parity arithmetic, the casewise diagonal-kill existence and its choice-function spec, closeness reflexivity) inlined verbatim above the target; the copy/demand/closeness/gate structures rely on the platform Definitions via imports.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem t6_assemble {DX DY : EReal × EReal → ℕ∞} (α ε : ℝ) (hε : 0 ≤ ε)
    (hDX : IsDiagramLike DX) (hDY : IsDiagramLike DY)
    (hFinX : {p : EReal × EReal | DX p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | DY p ≠ 0}.Finite)
    (hGX : ∃ F : {a : offD DX // DemandsOff α ε a} → offD DY,
        Function.Injective F ∧
        (∀ a, PromQNE α ε a.1 → CloseCopy2 ε a.1 (F a)) ∧
        (∀ a, offPt a.1 ∈ QSE α → CloseCopy1 ε a.1 (F a) ∧
          (offPt (F a) ∈ QNE α → CloseCopy2 ε a.1 (F a))))
    (hGY : ∃ F : {a : offD DY // DemandsOff α ε a} → offD DX,
        Function.Injective F ∧
        (∀ a, PromQNE α ε a.1 → CloseCopy2 ε a.1 (F a)) ∧
        (∀ a, offPt a.1 ∈ QSE α → CloseCopy1 ε a.1 (F a) ∧
          (offPt (F a) ∈ QNE α → CloseCopy2 ε a.1 (F a)))) :
    ∃ γ : Copies DX ≃ Copies DY, SatisfiesIIV γ α ε
    := by sorry
