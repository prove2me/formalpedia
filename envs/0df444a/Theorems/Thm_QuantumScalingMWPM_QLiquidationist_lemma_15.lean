-- Prove2me | Theorems.Thm_QuantumScalingMWPM_QLiquidationist_lemma_15
-- name    : QuantumScalingMWPM.QLiquidationist.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:15:49.136272+00:00
-- url     : https://prove2.me/theorems/eed8a1c1-0dd2-4a35-a5e1-f0208b91966d
-- title:
--   Lemma 15 — Task 3 runs in time $\tilde O(\sqrt{mn})$ (corrected: $\tilde O(n+\sqrt{mn})$)
-- statement:
--   There are constants $C>0$ and $\kappa\in\mathbb N$ with the following property. Let $M$ be a matching of $G$ ($n$ vertices, $m$ edges) and $\Omega$ a valid blossom family for $M$, and assume that there is no eligible augmenting path of blossoms in $G/\Omega$; this is the input of Task 3. Under the search accounting, every run of Algorithm 1 on this input satisfies two conditions:
--   1. its accumulated cost, plus the cost $1+\#\{\text{new blossoms}\}$ of promoting the new blossoms with $z(B)=0$, is at most
--   $$C\bigl(1+n+\sqrt{mn}\bigr)\bigl(\log_2(n+2)\bigr)^{\kappa}$$
--   at every point;
--   2. it can always continue until it terminates.
--
--   This is the second $\tilde O(\sqrt{mn})$ term of Theorem 2.
--
--   Differences from the source:
--   - correction: time Õ(√(mn)) → C · (1 + n + √(mn)) · (log₂(n+2))^k; reason: the printed bound is false for sparse graphs: on the graph with n ≥ 1 vertices and no edges (Ω = ∅, M = ∅) lines 4–5 of Algorithm 1 alone take n steps while √(mn) = 0; whenever m ≥ n/2 (in particular for every graph with a perfect matching) n ≤ √(2mn) and the corrected bound is the printed one; the additive 1 only matters at n = 0
--   - encoding: running time in the QRAM model, a GROVERSEARCH call charged by Lemma 1 → the search accounting of the PathSearch definition: a call over d_v neighbours with k marked ones costs ⌈√(d_v/k)⌉ (⌈√d_v⌉ if k = 0), every other elementary pseudocode step one unit; reason: the source's own accounting in the proof (Lemma 2's proof charges each call by Lemma 1, the rest as classical work); Õ hides the polylog factor (log₂(n+2))^k
--   - generalization: Algorithm 1 enumerates the free vertices (line 8) and the vertices of a blossom (foreach x ∈ V(B)) in an unspecified order → any order of the free vertices, and any enumeration order ord of each blossom (ValidOrd ord); reason: the source fixes no order; the statement for every order specializes to whatever order an implementation uses
--   - reading: the standing blossom invariant of §2.1 (p. 6: maintained "so that these facts always hold"; App. E, p. 39), not printed in the statement → hypotheses: M is a matching of G and Ω is a valid blossom family for M (IsBlossomFamily); reason: every call of the procedure in the source is made on such a structure; without it the objects of the statement (bases, blossom cycles) are undefined
--   - generalization: Task 3 (run after Task 2) → every valid input without an eligible augmenting path in G/Ω; reason: Task 3's input is such an input by Lemma 12; the statement specializes to it
--   - encoding: runs in time T → every reachable state's cost plus the promotion cost is ≤ T, and every non-final reachable state has a successor; reason: with unit cost per step, this says that every run terminates within cost T
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), Lemma 15, p. 22 (proof p. 22); §3.4, pp. 21–22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_PathSearch

namespace QuantumScalingMWPM.QLiquidationist

variable {n : ℕ}

/-- Lemma 15 (p. 22), corrected by an additive `n`. Task 3 (Algorithm 1 run on a matching and
blossom family without eligible augmenting path, followed by promoting its new blossoms with
`z = 0`) costs `O((n + √(mn)) polylog n)` at every point and always runs to completion. -/
theorem lemma_15 :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n) (y : Fin n → ℤ)
        (Ω : Family n) (ord : Finset (Fin n) → List (Fin n)),
        IsMatching G M → IsBlossomFamily G M Ω → ValidOrd ord →
        (∀ P, ¬ IsEligAugPathH G w M y Ω P) →
        ∀ s, Alg1Reach G w M y Ω ord s →
          ((s.cost + 1 + (s.fam.length - Ω.length) : ℕ) : ℝ) ≤
              C * (1 + n + Real.sqrt ((G.edgeSet.ncard : ℝ) * n)) *
                (Real.logb 2 ((n : ℝ) + 2)) ^ k ∧
            (s.done = false → ∃ s', Alg1Step G w M y Ω ord s s') := by sorry

end QuantumScalingMWPM.QLiquidationist
