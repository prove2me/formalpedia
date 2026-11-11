-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_corollary_5_4
-- name    : RWCuckoo.Threshold.corollary_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:32:20.07521+00:00
-- url     : https://prove2.me/theorems/2a9b3a12-bac4-4885-ae92-2eb23352d2e4
-- title:
--   Corollary 5.4 — the visitation lemma for the fresh-stopped walk, on the event of Lemma 4.2
-- statement:
--   There is an absolute constant $C$ such that for all $d\ge3$, $\varepsilon^*_d<\varepsilon\le1$ and large $n$ there is a hash-only event of probability at least $1-C/n$ on which the visitation lemma (Lemma 4.2) holds with constant $C$ and, moreover, for every admissible configuration $(M,F)$ and every set $G$ as in Lemma 4.2 (at least $7m/10$ occupied cells, or at least $m/2$ occupied cells if $d\ge10^6$), the fresh-stopped walk satisfies
--   $$\mathbb E\,T^{\mathrm{fresh}}\le C\,(1+\mathbb E\,N_G),$$
--   where $N_G$ is its number of visits to $G$ before it stops.
--
--   This is the form of the visitation lemma used by the regime theorems of Sections 5 and 6.
--
--   Differences from the source:
--   - encoding: m = ⌊(1 − ε)n⌋ keys (ε > ε∗_d) → hypothesis ε ≤ 1; reason: for ε > 1 the floor clamps the key count to 0, which is not the paper's setting; m = ⌊(1 − ε)n⌋ is a key count only for ε ≤ 1
--   - encoding: O(·), Ω(·), probability 1 − O(1/n) / 'w.h.p.' with absolute constants (footnote 2, p. 4; p. 5), 'for large n' → explicit constants ∃ C (and ∃ c > 0 for Ω) quantified before d and ε; ∃ n0 depending on d, ε (and the other fixed parameters) with ∀ n ≥ n0; probability bounds as μ(bad) ≤ ofReal(C/n); reason: the paper's definition of its asymptotic notation; one C serves several O's because every bound is monotone in C
--   - encoding: matching M : [m] → [n] injective with M(x) ∈ {h_1(x), …, h_d(x)} → Matching h records a matching index idx x with M(x) = h x (idx x); reason: every matching has such an index choice; the walks depend only on the cells, and an admissible configuration needs the matching index (Definition 5.2)
--   - encoding: admissible configuration (M, F): output of an adversary (Definition 5.2) → IsAdmissible M F: no matching probe (x, idx x) lies in F; reason: for given hashes these are exactly the pairs some adversary can output (examine the complement of F, output M)
--   - reading: 'On the event of Lemma 4.2', with the constant C of Lemma 4.2 → one event, of probability at least 1 − C/n, on which both Lemma 4.2's bound and the fresh-stopped bound hold with the same C; reason: Lemma 4.2's event is only asserted to exist; stating both bounds on one event is what 'on the event of Lemma 4.2' means
--   - generalization: standing assumption of Section 5, d ≥ D0 (p. 16) → every d ≥ 3; reason: the corollary lives on the event of Lemma 4.2, which exists for every d ≥ 3; its clause "if d ≥ 10^6" presupposes smaller d, and the paper says the proofs of App. C (every d ≥ 3) prove both statements; the statement for d ≥ 3 specializes to d ≥ D0
--   - encoding: E T^frozen, E T^fresh, E N_G (expectation over the walk, for fixed hashes and matching) → lintegral in ℝ≥0∞ of the ℕ∞-valued walk length or visit count against the uniform first cell × an i.i.d. uniform probe stream ℕ → Fin d (⊤ if the walk never stops); reason: the walk randomness of Definitions 2.1 and 5.3; expectations of possibly infinite lengths live in ℝ≥0∞
--   - encoding: on a hash-only event of probability 1 − O(1/n) (w.h.p.), the claim holds for every matching (configuration, set) → the uniform measure of the set of hash assignments of the first m keys on which the universal claim fails is at most C/n; reason: the claim involves only the first m keys; an event of all hashes on which it holds projects to a set of first-m hash assignments of at least the same probability, and the success set is itself a hash-only event (finite space)
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 18 (PDF 19), Corollary 5.4

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Corollary 5.4 (p. 18), on the event of Lemma 4.2: there is an absolute `C` such that for all
`d ≥ 3`, `ε∗_d < ε ≤ 1` and large `n`, a hash-only event of probability `1 − C/n` carries the
visitation lemma (Lemma 4.2) with constant `C` and, with the same `C`, for every admissible
configuration `(M, F)` and every `G` as in Lemma 4.2, `E T^fresh ≤ C (1 + E N_G)`, `N_G` the
fresh-stopped walk's number of visits to `G`. -/
theorem corollary_5_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d → ∀ ε : ℝ, epsStar d < ε → ε ≤ 1 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        hashMeasure (numKeys n ε) d n
            {h | ¬ ((∀ (M : Matching h) (G : Finset (Fin n)), G ⊆ M.occupied →
                (7 * (numKeys n ε : ℝ) / 10 ≤ G.card ∨
                  ((10 : ℕ) ^ 6 ≤ d ∧ (numKeys n ε : ℝ) / 2 ≤ G.card)) →
                expFrozenTime M ≤ ENNReal.ofReal C * (1 + expFrozenVisits M G)) ∧
              (∀ (M : Matching h) (F : Finset (Fin (numKeys n ε) × Fin d)) (G : Finset (Fin n)),
                IsAdmissible M F → G ⊆ M.occupied →
                (7 * (numKeys n ε : ℝ) / 10 ≤ G.card ∨
                  ((10 : ℕ) ^ 6 ≤ d ∧ (numKeys n ε : ℝ) / 2 ≤ G.card)) →
                expFreshTime M F ≤ ENNReal.ofReal C * (1 + expFreshVisits M F G)))} ≤
          ENNReal.ofReal (C / n) := by sorry

end RWCuckoo.Threshold
