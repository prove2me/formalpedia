-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_lemma_5_6
-- name    : RWCuckoo.Threshold.lemma_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:32:18.359685+00:00
-- url     : https://prove2.me/theorems/4dfd11e1-87f1-4a6a-968c-ac26f1276616
-- title:
--   Lemma 5.6 — restart: a bound B on E T^fresh for configurations with many fresh probes gives E[T^insertion | H_n] = O(B/ε)
-- statement:
--   Let $d\ge D_0$, $\varepsilon^*_d<\varepsilon\le1$, $0<r_1<r_2$ and $B\ge1$, and suppose:
--
--   **(R1)** w.h.p. (with an absolute constant $C_1$), every admissible configuration $(M,F)$ with $|F|\ge r_1m$ satisfies $\mathbb E\,T^{\mathrm{fresh}}\le B$;
--
--   **(R2)** except with probability $e^{-\Omega_{d,\varepsilon}(n)}$, if the first $m$ insertions finish, the prepared table has at least $r_2m$ fresh probes.
--
--   Then for all large $n$ there are hash-only events $H_n$ with $\Pr(H_n^c)\le C/n$ and
--   $$\mathbb E[T^{\mathrm{insertion}}\mid H_n]\le C\,\frac{B}{\varepsilon},$$
--   where $C$ depends only on $C_1$ (so it is absolute) and $D_0$ is absolute.
--
--   This is the restart argument shared by Sections 5 and 6: every fresh probe restarts the walk at a uniformly random cell, empty with probability about $\varepsilon$.
--
--   Differences from the source:
--   - encoding: m = ⌊(1 − ε)n⌋ keys (ε > ε∗_d) → hypothesis ε ≤ 1; reason: for ε > 1 the floor clamps the key count to 0, which is not the paper's setting; m = ⌊(1 − ε)n⌋ is a key count only for ε ≤ 1
--   - encoding: O(·), Ω(·), probability 1 − O(1/n) / 'w.h.p.' with absolute constants (footnote 2, p. 4; p. 5), 'for large n' → explicit constants ∃ C (and ∃ c > 0 for Ω) quantified before d and ε; ∃ n0 depending on d, ε (and the other fixed parameters) with ∀ n ≥ n0; probability bounds as μ(bad) ≤ ofReal(C/n); reason: the paper's definition of its asymptotic notation; one C serves several O's because every bound is monotone in C
--   - encoding: random hashes, random probe choices, T^insertion, E[T^insertion | H_n] → uniform measure on Fin (m+1) → Fin d → Fin n times an i.i.d. uniform probe stream ℕ → Fin d consumed in order by all insertions; T^insertion : ℕ∞ (⊤ if an insertion never ends); E[· | H_n] = lintegral of the ℝ≥0∞ coercion against ProbabilityTheory.cond; reason: the probability space the paper describes (pp. 4–5); expectations of an ℕ ∪ {∞}-valued cost live in ℝ≥0∞
--   - encoding: admissible configuration (M, F): output of an adversary (Definition 5.2) → IsAdmissible M F: no matching probe (x, idx x) lies in F; reason: for given hashes these are exactly the pairs some adversary can output (examine the complement of F, output M)
--   - encoding: standing assumption d ≥ D0 for a sufficiently large absolute D0 (pp. 13, 16) → ∃ D0 : ℕ, ∀ d ≥ D0; reason: the paper's 'sufficiently large absolute constant'; D0 ≥ 10^6 is implied by taking D0 larger
--   - reading: (R1) 'W.h.p.' (absolute hidden constant) and the conclusion's O(1/n), O(B/ε) → ∀ C₁, ∃ C > 0: (R1) with constant C₁ implies the conclusion with constant C; reason: the hypothesis's absolute constant is arbitrary; the conclusion's constants may depend on it and on nothing else
--   - encoding: (R2) 'except with probability e^{−Ω_{d,ε}(n)}' → ∃ c > 0, ∃ n2, ∀ n ≥ n2, Pr(first m insertions finish ∧ fresh probes < r2 m) ≤ exp(−c n); reason: c and n2 may depend on d, ε (and r2), as the subscript says
--   - encoding: E T^frozen, E T^fresh, E N_G (expectation over the walk, for fixed hashes and matching) → lintegral in ℝ≥0∞ of the ℕ∞-valued walk length or visit count against the uniform first cell × an i.i.d. uniform probe stream ℕ → Fin d (⊤ if the walk never stops); reason: the walk randomness of Definitions 2.1 and 5.3; expectations of possibly infinite lengths live in ℝ≥0∞
--   - encoding: on a hash-only event of probability 1 − O(1/n) (w.h.p.), the claim holds for every matching (configuration, set) → the uniform measure of the set of hash assignments of the first m keys on which the universal claim fails is at most C/n; reason: the claim involves only the first m keys; an event of all hashes on which it holds projects to a set of first-m hash assignments of at least the same probability, and the success set is itself a hash-only event (finite space)
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 19 (PDF 20), Lemma 5.6

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Lemma 5.6, restart (p. 19): let `d ≥ D0`, `ε∗_d < ε ≤ 1`, `0 < r1 < r2`, `B ≥ 1`. Suppose
(R1) w.h.p. (absolute constant `C₁`), every admissible configuration `(M, F)` with `|F| ≥ r1 m`
has `E T^fresh ≤ B`, and (R2) except with probability `e^{−Ω_{d,ε}(n)}`, if the first `m`
insertions finish they leave at least `r2 m` fresh probes. Then for large `n` there are hash-only
events `H_n` with `Pr(H_nᶜ) ≤ C/n` and `E[T^insertion | H_n] ≤ C B/ε`, `C` depending only on
`C₁`. -/
theorem lemma_5_6 :
    ∃ D0 : ℕ, ∀ C₁ : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, D0 ≤ d → ∀ ε : ℝ, epsStar d < ε → ε ≤ 1 →
      ∀ r1 r2 B : ℝ, 0 < r1 → r1 < r2 → 1 ≤ B →
      (∃ n1 : ℕ, ∀ n : ℕ, n1 ≤ n →
        hashMeasure (numKeys n ε) d n
            {h | ¬ ∀ (M : Matching h) (F : Finset (Fin (numKeys n ε) × Fin d)),
              IsAdmissible M F → r1 * numKeys n ε ≤ F.card →
              expFreshTime M F ≤ ENNReal.ofReal B} ≤
          ENNReal.ofReal (C₁ / n)) →
      (∃ c : ℝ, 0 < c ∧ ∃ n2 : ℕ, ∀ n : ℕ, n2 ≤ n →
        processMeasure (numKeys n ε + 1) d n
            {p | firstInsertionsFinish p.1 p.2 ∧ (freshLeft p.1 p.2 : ℝ) < r2 * numKeys n ε} ≤
          ENNReal.ofReal (Real.exp (-(c * n)))) →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ∃ H : Set (Hashes (numKeys n ε + 1) d n),
          hashMeasure (numKeys n ε + 1) d n Hᶜ ≤ ENNReal.ofReal (C / n) ∧
          condExpInsertionTime (numKeys n ε) d n H ≤ ENNReal.ofReal (C * B / ε) := by sorry

end RWCuckoo.Threshold
