-- Prove2me | Theorems.Thm_PolymatroidCover_theorem_1_1_exponential_time_covering
-- name    : PolymatroidCover.theorem_1_1_exponential_time_covering
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:53.475521+00:00
-- url     : https://prove2.me/theorems/7e289479-c38d-436f-82b1-b4f55ee688ec
-- title:
--   Theorem 1.1 — a covering by $(2d-1)\chi^\circ(f) - (2d-2)$ independent sets, found in exponential time
-- statement:
--   Let $f : 2^E \to \mathbb Z_{\ge 0}$ be a $d$-polymatroid (a monotone, submodular, integer-valued set function with $f(\emptyset) = 0$ and $f(e) \le d$ for every $e$), and let $\chi^\circ(f)$ be the lower bound of eq. (1). Write
--
--   $$
--   K := (2d - 1)\cdot\chi^\circ(f) - (2d - 2).
--   $$
--
--   **Theorem 1.1.** Given a value oracle for $f$, a covering of the ground set by at most $K$ independent sets of $f$ can be found in exponential time.
--
--   Both halves of the claim are stated, for every $n$, every $d$ and every $d$-polymatroid $f$ on $E = \{0, \dots, n-1\}$ with $f(E) > 0$:
--
--   1. **existence:** there is a coloring $c : E \to \{0, 1, \dots, K - 1\}$ whose color classes are all independent, i.e. a partition of $E$ into at most $K$ independent sets;
--   2. **exponential time:** there is one fixed program for the unit-cost value-oracle RAM `LSWNewArcAudit.NewArc`, using rational constants only, and one constant $C$, such that for every such $n$, $d$ and $f$ the program, started with $n$ in integer cell $0$ and given the value oracle of $f$, halts after at most $C \cdot 2^{C n}$ units of work (one per executed instruction, oracle queries and the halt included) and outputs such a coloring (the color of $e$ in integer cell $p + e$, where $p$ is the pointer returned by the halt instruction).
--
--   Since $\chi^\circ(f) \le \chi(f)$, this places the covering number within a factor $2d - 1$ of $\chi^\circ(f)$; for sums of $d$ matroid rank functions it gives a constructive version of the $(2d-1)$-approximate covering of Aharoni, Berger, Guo and Kotlar.
--
--   Differences from the source:
--   - encoding: a finite ground set $E$ and $f : 2^E \to \mathbb Z_{\ge 0}$ → `Fin n` and `f : Finset (Fin n) → ℕ`, marginals and deficiencies computed in `ℤ`; reason: Lean convention; the same instances
--   - encoding: $\chi^\circ(f)$, the maximum in (1), and no explicit assumption on $f(E)$ → `chiCirc f` (a `Finset.sup` of natural ceilings over the $T$ with $f(T) > 0$) together with the hypothesis $0 < f(E)$; reason: when $f(E) = 0$ the maximum in (1) is over the empty set and $\chi^\circ(f)$ is undefined; the hypothesis excludes exactly those instances, and for a polymatroid every ratio is nonnegative, so the sup is the max
--   - encoding: a covering of $E$ by at most $K$ independent sets → a coloring `c : Fin n → ℤ` with values in $[0, K)$ whose classes `{e | c e = j}` are independent; reason: a partition into at most $K$ independent sets is the same as such a coloring (empty classes allowed)
--   - reading: "given a value oracle … can be found in exponential time" (no machine model fixed) → one fixed `LiteralProgram` on the published oracle RAM `LSWNewArcAudit.NewArc`, given only $n$ (integer cell 0) and the oracle, halts with work $\le C\cdot 2^{C n}$, $C$ independent of $n$, $d$, $f$, and outputs the coloring in integer memory; reason: the paper names no machine; $2^{O(|E|)}$ uniform in $d$ and in the values of $f$ is the stronger reading of exponential time ($2^{\mathrm{poly}(|E|)}$ would be weaker), and the unit-cost oracle RAM charges every instruction and query
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), Theorem 1.1, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_PolymatroidCover_IsDPolymatroid
import Definitions.Def_PolymatroidCover_chiCirc
import Definitions.Def_PolymatroidCover_IsIndep
import Definitions.Def_PolymatroidCover_coverInput

namespace PolymatroidCover

/-- Theorem 1.1 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, printed p.3 = PDF p.5): given a value oracle for a
`d`-polymatroid `f`, a covering of the ground set by at most `(2d − 1)·χ°(f) − (2d − 2)`
independent sets of `f` can be found in exponential time.

Both halves of the claim are stated, for every `n`, every `d` and every `d`-polymatroid `f`
on `E = Fin n` with `f(E) > 0`, writing `K := (2d − 1)·χ°(f) − (2d − 2)` (in `ℤ`):
1. (existence) there is a coloring `c : E → {0, …, K − 1}` every color class of which is
   independent, i.e. a partition of `E` into at most `K` independent sets;
2. (exponential time) one fixed program of the published value-oracle RAM
   `LSWNewArcAudit.NewArc`, with rational literals only, given only `n` (integer cell `0`) and
   the value oracle of `f`, halts after at most `C·2^{C·n}` units of work (every executed
   instruction, oracle queries and the halt included; `C` independent of `n`, `d`, `f`) and
   outputs such a coloring (the color of `e` in integer cell `p + e`, `p` the halt pointer).

**Formalization Note** `0 < f univ` excludes exactly the instances for which the maximum in
eq. (1) is over the empty set. No self-loop hypothesis is assumed (Theorem 1.1 precedes the
standing assumption of §2). "Exponential time" is read as `2^{O(|E|)}` work, uniform in `d`
and in the values of `f`; the program receives neither `d` nor `K`. -/
theorem theorem_1_1_exponential_time_covering :
    (∀ (n d : ℕ) (f : Finset (Fin n) → ℕ), IsDPolymatroid d f → 0 < f Finset.univ →
      ∃ c : Fin n → ℤ,
        (∀ e : Fin n, 0 ≤ c e ∧ c e < (2 * (d : ℤ) - 1) * (chiCirc f : ℤ) - (2 * (d : ℤ) - 2)) ∧
        ∀ j : ℤ, IsIndep f (Finset.univ.filter (fun e => c e = j))) ∧
    (∃ program : LSWNewArcAudit.NewArc.OracleProgram,
      LSWNewArcAudit.NewArc.LiteralProgram program ∧
      ∃ C : ℕ, ∀ (n d : ℕ) (f : Finset (Fin n) → ℕ), IsDPolymatroid d f → 0 < f Finset.univ →
        ∃ (t : ℕ) (p : ℤ),
          let s := LSWNewArcAudit.NewArc.oracleRun program (fun X => (f X : ℤ)) (coverInput n) t
          s.output = some p ∧ s.work ≤ C * 2 ^ (C * n) ∧
          (∀ e : Fin n, 0 ≤ decodeColoring s p e ∧ decodeColoring s p e < (2 * (d : ℤ) - 1) * (chiCirc f : ℤ) - (2 * (d : ℤ) - 2)) ∧
          ∀ j : ℤ, IsIndep f (Finset.univ.filter (fun e => decodeColoring s p e = j))) := by sorry

end PolymatroidCover
