-- Prove2me | Theorems.Thm_TwoChoicesSuffice_KOut_lemma_15
-- name    : TwoChoicesSuffice.KOut.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:37.189663+00:00
-- url     : https://prove2.me/theorems/5af77b8e-f534-43e3-bfef-e09f7a79a297
-- title:
--   Lemma 15 — expected relevant-degree potential at most $11n$
-- statement:
--   Let $G$ be a finite simple graph on $n$ vertices. Under the marked two-out law, with $B^+=B^+(\sigma,S)$ the augmented base graph and $\Phi_R$ the relevant-degree component potential (order by increasing $d_v$, ties by a fixed order $\pi$),
--   $$
--   \mathbb E\bigl[\Phi_R(B^+)\bigr]\le 11n .
--   $$
--
--   This is the potential bound of the two-out case.
--
--   Differences from the source:
--   - generalization: graphs without isolated vertices (standing assumption of §3, PDF p. 7) → any finite simple graph; an isolated vertex makes the single dummy choice, adds no edge, and is counted in n; reason: isolated vertices are singleton components that own no edge and do not change the law on the other vertices, so on graphs without isolates the statement is exactly the source's, and with isolates its right side only grows
--   - encoding: a fixed total order π chosen independently of the sample and colouring → the LinearOrder instance of V, universally quantified; reason: a fixed deterministic order is independent of the randomness; every choice of π is covered
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), Lemma 15, printed p. 20, PDF p. 21

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling
import Definitions.Def_TwoChoicesSuffice_KOut_Potentials
import Definitions.Def_TwoChoicesSuffice_KOut_Leaders
import Definitions.Def_TwoChoicesSuffice_KOut_Coloring
import Definitions.Def_TwoChoicesSuffice_KOut_Marked

open scoped Classical

namespace TwoChoicesSuffice.KOut

/-- Lemma 15 (PDF p. 21, printed p. 20). For any simple graph `G`, under the marked
two-out law, `E[Φ_R(B⁺)] ≤ 11 n`. -/
theorem lemma_15 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) :
    markedExpect G (fun σ S => (relPotential G σ S (augBase G σ S) : ℝ)) ≤
      11 * (Fintype.card V : ℝ) := by sorry

end TwoChoicesSuffice.KOut
