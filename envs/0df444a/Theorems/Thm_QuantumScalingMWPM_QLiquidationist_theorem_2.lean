-- Prove2me | Theorems.Thm_QuantumScalingMWPM_QLiquidationist_theorem_2
-- name    : QuantumScalingMWPM.QLiquidationist.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:16:09.335662+00:00
-- url     : https://prove2.me/theorems/c66658bb-6ae1-409f-ac52-275df71affec
-- title:
--   Theorem 2 — QSEARCHONE runs in time $\tilde O(\sqrt{mn})$ (corrected: $\tilde O(n+\sqrt{mn})$)
-- statement:
--   There are constants $C>0$ and $\kappa\in\mathbb N$ with the following property. For every graph $G$ on $n$ vertices with $m$ edges, every matching $M$ of $G$, every valid blossom family $\Omega$ for $M$, all duals $y$, $z$, integer weights $w$ and every enumeration order:
--   1. QSEARCHONE has a run, that is, it terminates;
--   2. under the search accounting, every run of QSEARCHONE (Tasks 1–5, including lifting and augmenting along the paths found) costs at most
--   $$C\bigl(1+n+\sqrt{mn}\bigr)\bigl(\log_2(n+2)\bigr)^{\kappa}.$$
--
--   FREEVERTEXREDUCTION makes $\tau$ calls to QSEARCHONE per scale, so this bound gives Lemma 19.
--
--   Differences from the source:
--   - correction: time Õ(√(mn)) → C · (1 + n + √(mn)) · (log₂(n+2))^k; reason: the printed bound is false for sparse graphs: on the graph with n ≥ 1 vertices and no edges (Ω = ∅, M = ∅) lines 4–5 of Algorithm 1 alone take n steps while √(mn) = 0; whenever m ≥ n/2 (in particular for every graph with a perfect matching) n ≤ √(2mn) and the corrected bound is the printed one; the additive 1 only matters at n = 0
--   - encoding: running time in the QRAM model, a GROVERSEARCH call charged by Lemma 1 → the search accounting of the PathSearch definition: a call over d_v neighbours with k marked ones costs ⌈√(d_v/k)⌉ (⌈√d_v⌉ if k = 0), every other elementary pseudocode step one unit; reason: the source's own accounting in the proof (Lemma 2's proof charges each call by Lemma 1, the rest as classical work); Õ hides the polylog factor (log₂(n+2))^k
--   - generalization: Algorithm 1 enumerates the free vertices (line 8) and the vertices of a blossom (foreach x ∈ V(B)) in an unspecified order → any order of the free vertices, and any enumeration order ord of each blossom (ValidOrd ord); reason: the source fixes no order; the statement for every order specializes to whatever order an implementation uses
--   - reading: the standing blossom invariant of §2.1 (p. 6: maintained "so that these facts always hold"; App. E, p. 39), not printed in the statement → hypotheses: M is a matching of G and Ω is a valid blossom family for M (IsBlossomFamily); reason: every call of the procedure in the source is made on such a structure; without it the objects of the statement (bases, blossom cycles) are undefined
--   - encoding: the total running time of QSEARCHONE is T → some run exists, and every run has total cost ≤ T; reason: the runs of QSearchOne are its terminating executions; their existence is the termination claim
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), Theorem 2, p. 23 (proof p. 23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_PathSearch

namespace QuantumScalingMWPM.QLiquidationist

variable {n : ℕ}

/-- Theorem 2 (p. 23), corrected by an additive `n`. QSEARCHONE has a run, and every run costs
`O((n + √(mn)) polylog n)` in total (Tasks 1–5). -/
theorem theorem_2 :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ)
        (ord : Finset (Fin n) → List (Fin n)) (M : Mate n) (Ω : Family n) (y : Fin n → ℤ)
        (z : Finset (Fin n) → ℤ),
        IsMatching G M → IsBlossomFamily G M Ω → ValidOrd ord →
        (∃ r, QSearchOne G w ord M Ω y z r) ∧
          ∀ r, QSearchOne G w ord M Ω y z r →
            (r.cost : ℝ) ≤ C * (1 + n + Real.sqrt ((G.edgeSet.ncard : ℝ) * n)) *
              (Real.logb 2 ((n : ℝ) + 2)) ^ k := by sorry

end QuantumScalingMWPM.QLiquidationist
