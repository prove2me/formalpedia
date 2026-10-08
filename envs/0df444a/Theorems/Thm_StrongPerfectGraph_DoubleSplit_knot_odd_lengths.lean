-- Prove2me | Theorems.Thm_StrongPerfectGraph_DoubleSplit_knot_odd_lengths
-- name    : StrongPerfectGraph.DoubleSplit.knot_odd_lengths
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:29:19.771805+00:00
-- url     : https://prove2.me/theorems/645bbad6-a3bf-4354-8adc-1b5483022d45
-- title:
--   9.1, p. 108 — knots in Berge graphs have odd paths and antipaths, two of length one
-- statement:
--   Let $(P_1, P_2, Q_1, Q_2)$ be a knot in a Berge graph $G$. Then $P_1, P_2, Q_1, Q_2$ all have odd length, and
--
--   $$\bigl(|P_1| = |P_2| = 1\bigr) \ \text{or}\ \bigl(|Q_1| = |Q_2| = 1\bigr),$$
--
--   where $|P|$ is the length (number of edges) of a path or antipath.
--
--   Consequently a knot in a Berge graph is a degenerate appearance of $K_4$ in $G$ or in $\overline{G}$.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 108, 9.1

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_DoubleSplit_IsKnot

namespace StrongPerfectGraph.DoubleSplit

/-- 9.1 (p. 108): in a knot `(P₁, P₂, Q₁, Q₂)` of a Berge graph all four paths and antipaths have
odd length, and either `P₁, P₂` both have length one or `Q₁, Q₂` both have length one. The length
of a list is its number of vertices minus one. -/
theorem knot_odd_lengths {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : StrongPerfectGraph.Main.IsBerge G) (P₁ P₂ Q₁ Q₂ : List V) (hK : IsKnot G P₁ P₂ Q₁ Q₂) :
    (Odd (P₁.length - 1) ∧ Odd (P₂.length - 1) ∧ Odd (Q₁.length - 1) ∧ Odd (Q₂.length - 1)) ∧
    ((P₁.length - 1 = 1 ∧ P₂.length - 1 = 1) ∨ (Q₁.length - 1 = 1 ∧ Q₂.length - 1 = 1)) := by sorry

end StrongPerfectGraph.DoubleSplit
