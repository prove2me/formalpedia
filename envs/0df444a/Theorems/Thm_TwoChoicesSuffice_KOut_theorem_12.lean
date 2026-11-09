-- Prove2me | Theorems.Thm_TwoChoicesSuffice_KOut_theorem_12
-- name    : TwoChoicesSuffice.KOut.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:21.702454+00:00
-- url     : https://prove2.me/theorems/4d57c70e-89dd-4730-b51e-1b0226cc29d6
-- title:
--   Theorem 12 — $\mathbb E[x_G(H^2_G)]\le500n$
-- statement:
--   For every finite simple graph $G$ on $n$ vertices, its random two-out subgraph with replacement $H^2_G$ satisfies
--   $$
--   \mathbb E\bigl[x_G(H^2_G)\bigr]\le 500n .
--   $$
--
--   This is the case $k=2$ of Theorem 1, the threshold below which the bound fails.
--
--   Differences from the source:
--   - encoding: G arbitrary; isolated vertices removed without loss (§3, PDF p. 7) → isolated vertices kept, each with a single dummy choice that yields no edge, and counted in n; reason: deleting isolates changes neither the law on the other vertices nor the crossing edges and only decreases n; the Lean convention is that reduction, with no extra hypothesis
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), Theorem 12, printed p. 14, PDF p. 15

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling

open scoped Classical

namespace TwoChoicesSuffice.KOut

/-- Theorem 12 (PDF p. 15, printed p. 14). For every simple graph `G` on `n` vertices, its
random two-out subgraph with replacement satisfies `E[x_G(H^2_G)] ≤ 500 n`. -/
theorem theorem_12 {V : Type*} [Fintype V] (G : SimpleGraph V) :
    kOutExpect G 2 (fun σ => (crossingCount G (prefixGraph G σ 2) : ℝ)) ≤
      500 * (Fintype.card V : ℝ) := by sorry

end TwoChoicesSuffice.KOut
