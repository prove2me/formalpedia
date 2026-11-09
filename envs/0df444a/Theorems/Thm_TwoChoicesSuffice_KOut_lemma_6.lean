-- Prove2me | Theorems.Thm_TwoChoicesSuffice_KOut_lemma_6
-- name    : TwoChoicesSuffice.KOut.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:32.121744+00:00
-- url     : https://prove2.me/theorems/4b354339-180b-4f89-a4de-c5ccf44ad43e
-- title:
--   Lemma 6 — augmented two-out graph has expected potential at most $2n$
-- statement:
--   Let $G$ be a finite simple graph on $n$ vertices. Let $H^{2+}_G$ be the augmented two-out graph: each vertex makes three independent uniform choices with replacement, $H^2_G$ is the union of the first two, and the third choice of each $H^2_G$-leader (by increasing original degree, fixed tie-break) is added exactly when it reaches a higher $H^2_G$-component. Then
--   $$
--   \mathbb E\bigl[\Phi_G(H^{2+}_G)\bigr]\le 2n .
--   $$
--
--   This linear potential bound is the input of the refined switching inequality (Lemma 11).
--
--   Differences from the source:
--   - generalization: graphs without isolated vertices (standing assumption of §3, PDF p. 7) → any finite simple graph; an isolated vertex makes the single dummy choice, adds no edge, and is counted in n; reason: isolated vertices are singleton components that own no edge and do not change the law on the other vertices, so on graphs without isolates the statement is exactly the source's, and with isolates its right side only grows
--   - encoding: order by increasing original degree, ties broken arbitrarily → ties broken by the LinearOrder instance of V, quantified over every such order; reason: this is the source's 'arbitrary fixed tie-breaking order'; every instance of the source is an instance of the Lean statement
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), Lemma 6, printed p. 9, PDF p. 10

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling
import Definitions.Def_TwoChoicesSuffice_KOut_Potentials
import Definitions.Def_TwoChoicesSuffice_KOut_Leaders

open scoped Classical

namespace TwoChoicesSuffice.KOut

/-- Lemma 6 (PDF p. 10, printed p. 9). For any simple graph `G`,
`E[Φ_G(H^{2+}_G)] ≤ 2n`, where `H^{2+}_G` is the augmented two-out graph built from the
first three choices (each `H^2`-leader's third choice is added exactly when it reaches a
higher `H^2`-component). -/
theorem lemma_6 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) :
    kOutExpect G 3 (fun σ => (degPotential G (augTwoOut G σ) : ℝ)) ≤
      2 * (Fintype.card V : ℝ) := by sorry

end TwoChoicesSuffice.KOut
