-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_theorem_4_1
-- name    : RWCuckoo.Threshold.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:32:21.530571+00:00
-- url     : https://prove2.me/theorems/8234162c-23e9-495a-8964-e05c8df1ff0c
-- title:
--   Theorem 4.1 — insertion cost is O(1 + E T^frozen) on a hash-only event of probability 1 − O(1/n)
-- statement:
--   Let $d\ge3$ and $\varepsilon^*_d<\varepsilon\le1$, and put $m=\lfloor(1-\varepsilon)n\rfloor$. There is an absolute constant $C>0$ such that for all large $n$ there is an event $H_n$ of the hashes of the $m+1$ keys with $\Pr(H_n^c)\le C/n$ and the following property. Let $h$ be a value of the hashes $H_0$ of the first $m$ keys with $\Pr(H_n\mid H_0=h)>0$ and let $M$ be a matching of these keys. Then
--   $$\mathbb E\bigl[T^{\mathrm{insertion}}\mid H_0=h,\ H_n,\ M\bigr]\;\le\;C\bigl(1+\mathbb E[T^{\mathrm{frozen}}\mid H_0=h,\ M]\bigr),$$
--   where on the left the expectation is over the new key's hashes (conditioned on $H_n$ given $H_0=h$) and the insertion's probe choices, the insertion starting from the table given by $M$, and on the right over the frozen-matching walk on $M$.
--
--   This is the paper's bridge from actual insertions to the frozen-matching walk; averaged over $h$ and the prepared matching it reduces every regime theorem to a bound on $\mathbb E\,T^{\mathrm{frozen}}$ or on the fresh-stopped walk.
--
--   Differences from the source:
--   - encoding: m = ⌊(1 − ε)n⌋ keys (ε > ε∗_d) → hypothesis ε ≤ 1; reason: for ε > 1 the floor clamps the key count to 0, which is not the paper's setting; m = ⌊(1 − ε)n⌋ is a key count only for ε ≤ 1
--   - encoding: O(·), Ω(·), probability 1 − O(1/n) / 'w.h.p.' with absolute constants (footnote 2, p. 4; p. 5), 'for large n' → explicit constants ∃ C (and ∃ c > 0 for Ω) quantified before d and ε; ∃ n0 depending on d, ε (and the other fixed parameters) with ∀ n ≥ n0; probability bounds as μ(bad) ≤ ofReal(C/n); reason: the paper's definition of its asymptotic notation; one C serves several O's because every bound is monotone in C
--   - encoding: random hashes, random probe choices, T^insertion, E[T^insertion | H_n] → uniform measure on Fin (m+1) → Fin d → Fin n times an i.i.d. uniform probe stream ℕ → Fin d consumed in order by all insertions; T^insertion : ℕ∞ (⊤ if an insertion never ends); E[· | H_n] = lintegral of the ℝ≥0∞ coercion against ProbabilityTheory.cond; reason: the probability space the paper describes (pp. 4–5); expectations of an ℕ ∪ {∞}-valued cost live in ℝ≥0∞
--   - reading: a matching M chosen without looking at the new key's hashes → every fixed matching M of the first m keys; reason: a matching chosen independently of the new key's hashes is a mixture of fixed matchings; the statement for each fixed one gives it
--   - encoding: Pr(H_n | H_0 = h) > 0 → the uniform measure of {g | withNewKey h g ∈ H_n} is nonzero; reason: the hashes are uniform and independent, so the conditional law of the new key's hashes given H_0 = h is uniform
--   - encoding: matching M : [m] → [n] injective with M(x) ∈ {h_1(x), …, h_d(x)} → Matching h records a matching index idx x with M(x) = h x (idx x); reason: every matching has such an index choice; the walks depend only on the cells, and an admissible configuration needs the matching index (Definition 5.2)
--   - encoding: E T^frozen, E T^fresh, E N_G (expectation over the walk, for fixed hashes and matching) → lintegral in ℝ≥0∞ of the ℕ∞-valued walk length or visit count against the uniform first cell × an i.i.d. uniform probe stream ℕ → Fin d (⊤ if the walk never stops); reason: the walk randomness of Definitions 2.1 and 5.3; expectations of possibly infinite lengths live in ℝ≥0∞
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 13 (PDF 14), Theorem 4.1

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Theorem 4.1 (p. 13): there is an absolute `C > 0` such that for every `d ≥ 3` and
`ε∗_d < ε ≤ 1` and all large `n` there is an event `H_n` of the hashes of the `m + 1` keys with
`Pr(H_nᶜ) ≤ C/n` such that, for every value `h` of the hashes of the first `m` keys with
`Pr(H_n | H_0 = h) > 0` and every matching `M` of these keys, the expected cost of inserting the
new key into the table `M` (over the new key's hashes given `H_0 = h` and `H_n`, and the
insertion's probe choices) is at most `C (1 + E[T^frozen | H_0 = h, M])`. -/
theorem theorem_4_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d → ∀ ε : ℝ, epsStar d < ε → ε ≤ 1 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ∃ H : Set (Hashes (numKeys n ε + 1) d n),
          hashMeasure (numKeys n ε + 1) d n Hᶜ ≤ ENNReal.ofReal (C / n) ∧
          ∀ h : Hashes (numKeys n ε) d n,
            (uniformOn Set.univ : Measure (Fin d → Fin n)) {g | withNewKey h g ∈ H} ≠ 0 →
            ∀ M : Matching h,
              ∫⁻ p, ((insertionCost (withNewKey h p.1) M.table (Fin.last _) p.2 : ℕ∞) : ℝ≥0∞)
                  ∂(((uniformOn Set.univ : Measure (Fin d → Fin n))[|{g | withNewKey h g ∈ H}]).prod
                    (streamMeasure d)) ≤
                ENNReal.ofReal C * (1 + expFrozenTime M) := by sorry

end RWCuckoo.Threshold
