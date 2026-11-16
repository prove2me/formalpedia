-- Prove2me | Theorems.Thm_PolymatroidCover_Supplement_theorem_1_3_packing_generators
-- name    : PolymatroidCover.Supplement.theorem_1_3_packing_generators
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:52:53.992525+00:00
-- url     : https://prove2.me/theorems/5b0611df-3cc9-4581-9b68-0dd5dc7e163e
-- title:
--   Theorem 1.3 — $\kappa(f) \ge \lfloor \kappa^\circ(f)/d \rfloor$, and such a packing is found in polynomial time
-- statement:
--   Let $f : 2^E \to \mathbb Z_{\ge 0}$ be a $d$-polymatroid on $E = \{0,\dots,n-1\}$ with $f(E) > 0$, let $\kappa^\circ(f)$ be the packing upper bound of eq. (2) (with its floor), and let $\kappa(f)$ be the maximum number of pairwise disjoint generators of $f$. Then:
--
--   1. **(existence)**
--   $$
--   \kappa(f) \ge \left\lfloor \frac{\kappa^\circ(f)}{d} \right\rfloor,
--   $$
--   that is, $f$ has $\lfloor \kappa^\circ(f)/d \rfloor$ pairwise disjoint generators;
--   2. **(polynomial time)** there is one fixed program for the unit-cost value-oracle RAM which, given only $n$ and a value oracle for $f$, halts after a number of steps bounded by a polynomial in $n$ (independent of $d$ and of the values of $f$) and outputs a family of at least $\lfloor \kappa^\circ(f)/d \rfloor$ pairwise disjoint generators of $f$.
--
--   Since $\kappa(f) \le \kappa^\circ(f)$, this is an $O(d)$-approximation for packing generators of a $d$-polymatroid, answering the question of Călinescu, Chekuri and Vondrák whether an approximation depending only on $d$ (rather than on $f(E)$) exists.
--
--   **Formalization Note** The output format is the decoder `packingCount` / `packingSet`: a number $q$ and a label per element; the sets with labels $0,\dots,q-1$ are pairwise disjoint by construction. No self-loop assumption is made: the theorem is first stated in §1.1, before the standing assumption of §2.
--
--   Differences from the source:
--   - encoding: ground set E, f : 2^E → Z≥0 → E = Fin n, f : Finset (Fin n) → ℕ; reason: the mission's published convention; same instances
--   - encoding: f with f(E) > 0 implicit (the bound is defined only then) → hypothesis 0 < f univ; reason: it excludes exactly the instances for which the optimum in the defining equation is over the empty set and undefined
--   - encoding: κ(f) ≥ ⌊κ°(f)/d⌋, κ(f) the maximum number of pairwise disjoint generators → there exist ⌊κ°(f)/d⌋ pairwise disjoint generators G : Fin (kappaCirc f / d) → Finset (Fin n); reason: κ(f) ≥ q iff q pairwise disjoint generators exist; avoids defining κ as a supremum
--   - reading: can be found in polynomial time, given a value oracle → one fixed LiteralProgram on the published unit-cost value-oracle RAM LSWNewArcAudit.NewArc, input coverInput n only, halting with work ≤ C·(n+1)^C (C independent of n, d, f); the output, decoded by packingCount / packingSet, is a family of at least ⌊κ°(f)/d⌋ sets each of which is a generator; reason: the machine and input of the published Theorem 1.1; the decoded sets are pairwise disjoint by construction; d and κ°(f) are not given to the program
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), Theorem 1.3, p.26 (PDF p.28), proof §5 pp.26–27; first stated p.4 (PDF p.6)

import Mathlib
import Definitions.Def_PolymatroidCover_IsDPolymatroid
import Definitions.Def_PolymatroidCover_coverInput
import Definitions.Def_PolymatroidCover_Supplement_IsGenerator
import Definitions.Def_PolymatroidCover_Supplement_kappaCirc
import Definitions.Def_PolymatroidCover_Supplement_packingSet

namespace PolymatroidCover.Supplement

open PolymatroidCover

/-- Theorem 1.3 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §5, printed p.26 = PDF p.28; also §1.1, printed p.4 = PDF p.6): "For every
`d`-polymatroid `f`, `κ(f) ≥ ⌊κ°(f)/d⌋`. Moreover, given a value oracle for `f`, a family of at
least `⌊κ°(f)/d⌋` pairwise disjoint generators can be found in polynomial time."

Both halves are stated, for every `n`, every `d` and every `d`-polymatroid `f` on `E = Fin n`
with `f(E) > 0`, writing `q := ⌊κ°(f)/d⌋`:
1. (`κ(f) ≥ q`) there are `q` pairwise disjoint generators `G_0, …, G_{q−1}` of `f`;
2. (polynomial time) one fixed program of the published value-oracle RAM `LSWNewArcAudit.NewArc`,
   with rational literals only, given only `n` (integer cell `0`) and the value oracle of `f`,
   halts after at most `C·(n + 1)^C` units of work (`C` independent of `n`, `d`, `f`) and outputs
   a family of at least `q` sets each of which is a generator; the sets are pairwise disjoint by
   the decoder (`packingCount`, `packingSet`).

**Formalization Note** `κ(f)`, the maximum number of pairwise disjoint generators, is not defined;
`κ(f) ≥ q` is stated as the existence of `q` pairwise disjoint generators, which is equivalent.
`⌊κ°(f)/d⌋` is natural division. `0 < f univ` excludes exactly the instances for which the minimum
in eq. (2) is over the empty set. No self-loop hypothesis is assumed. "Polynomial time" is read as
work polynomial in `|E|` on the unit-cost oracle RAM, uniform in `d` and in the values of `f`; the
program receives neither `d` nor `κ°(f)`. -/
theorem theorem_1_3_packing_generators :
    (∀ (n d : ℕ) (f : Finset (Fin n) → ℕ), IsDPolymatroid d f → 0 < f Finset.univ →
      ∃ G : Fin (kappaCirc f / d) → Finset (Fin n),
        (∀ i j, i ≠ j → Disjoint (G i) (G j)) ∧ ∀ i, IsGenerator f (G i)) ∧
    (∃ program : LSWNewArcAudit.NewArc.OracleProgram,
      LSWNewArcAudit.NewArc.LiteralProgram program ∧
      ∃ C : ℕ, ∀ (n d : ℕ) (f : Finset (Fin n) → ℕ), IsDPolymatroid d f → 0 < f Finset.univ →
        ∃ (t : ℕ) (p : ℤ),
          let s := LSWNewArcAudit.NewArc.oracleRun program (fun X => (f X : ℤ)) (coverInput n) t
          s.output = some p ∧ s.work ≤ C * (n + 1) ^ C ∧
          ((kappaCirc f / d : ℕ) : ℤ) ≤ packingCount s p ∧
          ∀ i : ℤ, 0 ≤ i → i < packingCount s p → IsGenerator f (packingSet s p i)) := by sorry

end PolymatroidCover.Supplement
