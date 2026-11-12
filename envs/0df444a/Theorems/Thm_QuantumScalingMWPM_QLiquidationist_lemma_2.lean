-- Prove2me | Theorems.Thm_QuantumScalingMWPM_QLiquidationist_lemma_2
-- name    : QuantumScalingMWPM.QLiquidationist.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:15:52.482988+00:00
-- url     : https://prove2.me/theorems/b75e643b-2398-434b-bd1b-6c18b79015d2
-- title:
--   Lemma 2 — QUANTUMPATHSEARCH runs in time $\tilde O(\sqrt{mn})$ (corrected: $\tilde O(n+\sqrt{mn})$)
-- statement:
--   There are constants $C>0$ and $\kappa\in\mathbb N$ with the following property. Let $G$ be any graph on $n$ vertices with $m$ edges, $M$ a matching of $G$, $\Omega$ a valid blossom family for $M$, $y$ vertex duals, $w$ integer weights, and any enumeration order. Under the search accounting (a GROVERSEARCH call over $d_v$ neighbours with $k$ marked ones costs $\lceil\sqrt{d_v/k}\rceil$, or $\lceil\sqrt{d_v}\rceil$ if $k=0$, and every other elementary step one unit), every run of Algorithm 1 (QUANTUMPATHSEARCH) satisfies two conditions:
--   1. at every point its accumulated cost is at most
--   $$C\bigl(1+n+\sqrt{mn}\bigr)\bigl(\log_2(n+2)\bigr)^{\kappa};$$
--   2. it can always continue until it terminates.
--
--   When $m\ge n/2$, in particular for every graph with a perfect matching, $n\le\sqrt{2mn}$ and the bound is $\tilde O(\sqrt{mn})$ as printed. This bound gives the $\tilde O(\tau\sqrt{mn}\log W)$ cost of FREEVERTEXREDUCTION.
--
--   Differences from the source:
--   - correction: time Õ(√(mn)) → C · (1 + n + √(mn)) · (log₂(n+2))^k; reason: the printed bound is false for sparse graphs: on the graph with n ≥ 1 vertices and no edges (Ω = ∅, M = ∅) lines 4–5 of Algorithm 1 alone take n steps while √(mn) = 0; whenever m ≥ n/2 (in particular for every graph with a perfect matching) n ≤ √(2mn) and the corrected bound is the printed one; the additive 1 only matters at n = 0
--   - encoding: running time in the QRAM model, a GROVERSEARCH call charged by Lemma 1 → the search accounting of the PathSearch definition: a call over d_v neighbours with k marked ones costs ⌈√(d_v/k)⌉ (⌈√d_v⌉ if k = 0), every other elementary pseudocode step one unit; reason: the source's own accounting in the proof (Lemma 2's proof charges each call by Lemma 1, the rest as classical work); Õ hides the polylog factor (log₂(n+2))^k
--   - generalization: Algorithm 1 enumerates the free vertices (line 8) and the vertices of a blossom (foreach x ∈ V(B)) in an unspecified order → any order of the free vertices, and any enumeration order ord of each blossom (ValidOrd ord); reason: the source fixes no order; the statement for every order specializes to whatever order an implementation uses
--   - reading: the standing blossom invariant of §2.1 (p. 6: maintained "so that these facts always hold"; App. E, p. 39), not printed in the statement → hypotheses: M is a matching of G and Ω is a valid blossom family for M (IsBlossomFamily); reason: every call of the procedure in the source is made on such a structure; without it the objects of the statement (bases, blossom cycles) are undefined
--   - encoding: runs in time T → every reachable state has cost ≤ T, and every non-final reachable state has a successor; reason: with unit cost per step, this says that every run terminates within cost T
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), Lemma 2, p. 12 (proof p. 12; uses Lemmas 9–11, pp. 19–20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_PathSearch

namespace QuantumScalingMWPM.QLiquidationist

variable {n : ℕ}

/-- Lemma 2 (p. 12), corrected by an additive `n`. Under the search accounting, every run of
QUANTUMPATHSEARCH costs `O((n + √(mn)) polylog n)` at every point and can always continue until
it terminates. -/
theorem lemma_2 :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n) (y : Fin n → ℤ)
        (Ω : Family n) (ord : Finset (Fin n) → List (Fin n)),
        IsMatching G M → IsBlossomFamily G M Ω → ValidOrd ord →
        ∀ s, Alg1Reach G w M y Ω ord s →
          (s.cost : ℝ) ≤ C * (1 + n + Real.sqrt ((G.edgeSet.ncard : ℝ) * n)) *
              (Real.logb 2 ((n : ℝ) + 2)) ^ k ∧
            (s.done = false → ∃ s', Alg1Step G w M y Ω ord s s') := by sorry

end QuantumScalingMWPM.QLiquidationist
