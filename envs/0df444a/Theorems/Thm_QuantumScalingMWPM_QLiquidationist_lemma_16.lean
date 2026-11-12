-- Prove2me | Theorems.Thm_QuantumScalingMWPM_QLiquidationist_lemma_16
-- name    : QuantumScalingMWPM.QLiquidationist.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:16:08.606579+00:00
-- url     : https://prove2.me/theorems/e6377435-f463-482f-b69c-e244a235ddf7
-- title:
--   Lemma 16 — dual adjustment and blossom dissolution take $O(n)$ time
-- statement:
--   There is a constant $C>0$ such that for every graph $G$ on $n$ vertices, every matching $M$ of $G$, every valid blossom family $\Omega$ for $M$, all duals $y$, $z$ and every run of QSEARCHONE, the cost of Tasks 4 and 5 is at most $C(1+n)$. Task 4 is the dual adjustment $y(v)\mp1$ on OUT/IN vertices and $z(B)\pm2$ on OUT/IN root blossoms. Task 5 dissolves the root blossoms with $z(B)=0$ and rebuilds ROOTB by one traversal of the blossom forest.
--
--   There is no polylogarithmic factor: this bound is exactly linear. It is the $O(n)$ term of Theorem 2.
--
--   Differences from the source:
--   - reading: the standing blossom invariant of §2.1 (p. 6: maintained "so that these facts always hold"; App. E, p. 39), not printed in the statement → hypotheses: M is a matching of G and Ω is a valid blossom family for M (IsBlossomFamily); reason: every call of the procedure in the source is made on such a structure; without it the objects of the statement (bases, blossom cycles) are undefined
--   - generalization: Algorithm 1 enumerates the free vertices (line 8) and the vertices of a blossom (foreach x ∈ V(B)) in an unspecified order → any order of the free vertices, and any enumeration order ord of each blossom (ValidOrd ord); reason: the source fixes no order; the statement for every order specializes to whatever order an implementation uses
--   - encoding: the dual adjustment and blossom dissolution take O(n) time → their charge (1 + n + |Ω₃|) + (1 + n + |Ω₃| + Σ children) is at most C(1 + n), Ω₃ the family after Task 3; reason: one unit per vertex, per blossom record and per child visited, which is the linear-time implementation the source cites from [13]; the additive 1 only matters at n = 0
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), Lemma 16, p. 22 (proof p. 22); §3.5, p. 22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_PathSearch

namespace QuantumScalingMWPM.QLiquidationist

variable {n : ℕ}

/-- Lemma 16 (p. 22). The dual adjustment and blossom dissolution of QSEARCHONE (Tasks 4–5) take
`O(n)` time. -/
theorem lemma_16 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ)
        (ord : Finset (Fin n) → List (Fin n)) (M : Mate n) (Ω : Family n) (y : Fin n → ℤ)
        (z : Finset (Fin n) → ℤ) (r : QSOneResult n),
        IsMatching G M → IsBlossomFamily G M Ω → ValidOrd ord →
        QSearchOne G w ord M Ω y z r → (r.cost45 : ℝ) ≤ C * (1 + n) := by sorry

end QuantumScalingMWPM.QLiquidationist
