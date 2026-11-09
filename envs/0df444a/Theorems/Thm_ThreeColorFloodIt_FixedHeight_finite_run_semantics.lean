-- Prove2me | Theorems.Thm_ThreeColorFloodIt_FixedHeight_finite_run_semantics
-- name    : ThreeColorFloodIt.FixedHeight.finite_run_semantics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:23.981575+00:00
-- url     : https://prove2.me/theorems/5873a0a0-3219-4fa7-86a5-96ce708f11bc
-- title:
--   Lemma 18 — Finite grammar witnesses and budget preservation
-- statement:
--   For elementary weighted pushdown rules with nonnegative integer costs, finite derivations using equations (3)–(5) and frame-removing subruns have exactly the same attainable costs in both directions:
--   $$D[p,A,q]\text{ is witnessed by precisely the finite grammar derivations}.$$
--   The correspondence holds above any fixed suffix, which no rule reads or changes. For every total cost $d\le M$, retaining only derivations whose subtree values are at most $M$ preserves exactly those frame-removing computations, including accepting computations from the bottom marker. Finite inductive witnesses exclude self-supporting zero-cost cycles.
--
--   Differences from the source:
--   - generalization: the finite four-symbol pushdown system constructed for the board → any control carrier with elementary nonnegative-cost rules on the same four-symbol alphabet; reason: the finite derivation/frame argument is independent of the number of controls; the constructed finite system is an instance
--   - encoding: finite runs above an untouched suffix and the recurrence (3)–(5) → inductive frame runs, finite derivation trees and capped finite trees; reason: each constructor is an actual elementary step or a finite composition; B is on top in BC and no infinite witness is admitted
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 15 (PDF 16), Lemma 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf

import Definitions.Def_ThreeColorFloodIt_FixedHeight_grammar

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

theorem finite_run_semantics {Q : Type} (S : WeightedPDS Q)
    (elementary : ∀ r ∈ S, Elementary r) :
    (∀ (p q : Q) (A : StackSymbol) (d : ℕ) (suffix : List StackSymbol),
      Derivation S p A q d ↔ FrameRun S suffix p [A] q d) ∧
    (∀ (M : ℕ) (p q : Q) (A : StackSymbol) (d : ℕ), d ≤ M →
      (CappedDerivation S M p A q d ↔ FrameRun S [] p [A] q d)) := by sorry

end ThreeColorFloodIt.FixedHeight
