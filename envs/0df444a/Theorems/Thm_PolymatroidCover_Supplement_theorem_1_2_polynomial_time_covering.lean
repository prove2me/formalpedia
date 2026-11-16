-- Prove2me | Theorems.Thm_PolymatroidCover_Supplement_theorem_1_2_polynomial_time_covering
-- name    : PolymatroidCover.Supplement.theorem_1_2_polynomial_time_covering
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:51:45.491729+00:00
-- url     : https://prove2.me/theorems/a9e28304-62d5-4f0f-9aed-3372cfd4022b
-- title:
--   Theorem 1.2 — a covering by $(4d-2)\chi^\circ(f)$ independent sets, found in polynomial time
-- statement:
--   Let $f : 2^E \to \mathbb Z_{\ge 0}$ be a $d$-polymatroid on the ground set $E = \{0,\dots,n-1\}$ with $f(E) > 0$, and let $\chi^\circ(f)$ be the covering lower bound of eq. (1) (with its ceiling). Then:
--
--   1. **(existence)** $E$ can be partitioned into at most
--   $$
--   (4d-2)\cdot\chi^\circ(f)
--   $$
--   independent sets of $f$;
--   2. **(polynomial time)** there is one fixed program for the unit-cost value-oracle RAM which, given only $n$ and a value oracle for $f$, halts after a number of steps bounded by a polynomial in $n$ (independent of $d$ and of the values of $f$) and outputs such a partition, as a coloring of $E$ with colors in $\{0, \dots, (4d-2)\chi^\circ(f)-1\}$ whose color classes are independent.
--
--   Compared with Theorem 1.1 the number of sets grows from $(2d-1)\chi^\circ(f)-(2d-2)$ to $(4d-2)\chi^\circ(f)$, and exponential time becomes polynomial time. For the intersection of $d$ matroids this gives a polynomial-time $(4d-2)$-approximate covering by common independent sets.
--
--   **Formalization Note** The machine, input layout and output decoder are those of the published Theorem 1.1. No self-loop assumption is made: Theorem 1.2 is stated in §1.1, before the standing assumption of §2.
--
--   Differences from the source:
--   - encoding: ground set E, f : 2^E → Z≥0 → E = Fin n, f : Finset (Fin n) → ℕ; reason: the mission's published convention; same instances
--   - encoding: f with f(E) > 0 implicit (the bound is defined only then) → hypothesis 0 < f univ; reason: it excludes exactly the instances for which the optimum in the defining equation is over the empty set and undefined
--   - reading: can be found in polynomial time, given a value oracle → one fixed LiteralProgram on the published unit-cost value-oracle RAM LSWNewArcAudit.NewArc, input coverInput n only, halting with work ≤ C·(n+1)^C (C independent of n, d, f) and output decoded by decodeColoring; reason: the same machine, input and decoder as the published Theorem 1.1, with the exponential bound replaced by a polynomial one; d, χ°(f) and the number of colors are not given to the program
--   - encoding: a covering by at most (4d − 2)·χ°(f) independent sets → a coloring c : E → ℤ with 0 ≤ c(e) < (4d − 2)·χ°(f) whose color classes are independent; reason: a partition into at most K independent sets is a coloring with K colors (empty classes are independent)
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), Theorem 1.2, p.3 (PDF p.5); proof via Algorithm 2 and Theorem 4.1, §4, pp.20–26 (PDF pp.22–28)

import Mathlib
import Definitions.Def_PolymatroidCover_IsDPolymatroid
import Definitions.Def_PolymatroidCover_chiCirc
import Definitions.Def_PolymatroidCover_IsIndep
import Definitions.Def_PolymatroidCover_coverInput

namespace PolymatroidCover.Supplement

open PolymatroidCover

/-- Theorem 1.2 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, printed p.3 = PDF p.5): "Given a value oracle for a
`d`-polymatroid `f`, a covering of the ground set by at most `(4d − 2) · χ°(f)` independent sets
of `f` can be found in polynomial time."

Both halves of the claim are stated, for every `n`, every `d` and every `d`-polymatroid `f` on
`E = Fin n` with `f(E) > 0`, writing `K := (4d − 2)·χ°(f)` (in `ℤ`):
1. (existence) there is a coloring `c : E → {0, …, K − 1}` every color class of which is
   independent, i.e. a partition of `E` into at most `K` independent sets;
2. (polynomial time) one fixed program of the published value-oracle RAM
   `LSWNewArcAudit.NewArc`, with rational literals only, given only `n` (integer cell `0`) and the
   value oracle of `f`, halts after at most `C·(n + 1)^C` units of work (every executed
   instruction, oracle queries and the halt included; `C` independent of `n`, `d`, `f`) and
   outputs such a coloring (the color of `e` in integer cell `p + e`, `p` the halt pointer).

**Formalization Note** `0 < f univ` excludes exactly the instances for which the maximum in eq. (1)
is over the empty set. No self-loop hypothesis is assumed (Theorem 1.2 precedes the standing
assumption of §2). "Polynomial time" is read as work polynomial in `|E|` on the unit-cost oracle
RAM, uniform in `d` and in the values of `f`; the program receives neither `d` nor `K`. The input
layout and the output decoder are the published `coverInput` / `decodeColoring` of Theorem 1.1. -/
theorem theorem_1_2_polynomial_time_covering :
    (∀ (n d : ℕ) (f : Finset (Fin n) → ℕ), IsDPolymatroid d f → 0 < f Finset.univ →
      ∃ c : Fin n → ℤ,
        (∀ e : Fin n, 0 ≤ c e ∧ c e < (4 * (d : ℤ) - 2) * (chiCirc f : ℤ)) ∧
        ∀ j : ℤ, IsIndep f (Finset.univ.filter (fun e => c e = j))) ∧
    (∃ program : LSWNewArcAudit.NewArc.OracleProgram,
      LSWNewArcAudit.NewArc.LiteralProgram program ∧
      ∃ C : ℕ, ∀ (n d : ℕ) (f : Finset (Fin n) → ℕ), IsDPolymatroid d f → 0 < f Finset.univ →
        ∃ (t : ℕ) (p : ℤ),
          let s := LSWNewArcAudit.NewArc.oracleRun program (fun X => (f X : ℤ)) (coverInput n) t
          s.output = some p ∧ s.work ≤ C * (n + 1) ^ C ∧
          (∀ e : Fin n, 0 ≤ decodeColoring s p e ∧ decodeColoring s p e < (4 * (d : ℤ) - 2) * (chiCirc f : ℤ)) ∧
          ∀ j : ℤ, IsIndep f (Finset.univ.filter (fun e => decodeColoring s p e = j))) := by sorry

end PolymatroidCover.Supplement
