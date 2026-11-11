-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_theorem_5_1
-- name    : RWCuckoo.Threshold.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:32:19.057948+00:00
-- url     : https://prove2.me/theorems/5f5f73f6-f163-4ea5-9579-9028821e2a2d
-- title:
--   Theorem 5.1 — large ε ≥ e^{−d/4}: E[T^insertion | H_n] = O(1/ε)
-- statement:
--   There are absolute constants $D_0$ and $C>0$ such that for $d\ge D_0$ and $\varepsilon^*_d<\varepsilon\le1$ with $\varepsilon\ge e^{-d/4}$ there is a threshold $n_0(d,\varepsilon)$ and, for every $n\ge n_0$, a hash-only event $H_n$ with $\Pr(H_n^c)\le C/n$ and
--   $$\mathbb E[T^{\mathrm{insertion}}\mid H_n]\le \frac{C}{\varepsilon}.$$
--
--   This proves Theorem 1.1 for $\varepsilon\ge e^{-d/4}$ and is the regime treated by stopping the walk at a fresh probe.
--
--   Differences from the source:
--   - encoding: m = ⌊(1 − ε)n⌋ keys (ε > ε∗_d) → hypothesis ε ≤ 1; reason: for ε > 1 the floor clamps the key count to 0, which is not the paper's setting; m = ⌊(1 − ε)n⌋ is a key count only for ε ≤ 1
--   - encoding: O(·), Ω(·), probability 1 − O(1/n) / 'w.h.p.' with absolute constants (footnote 2, p. 4; p. 5), 'for large n' → explicit constants ∃ C (and ∃ c > 0 for Ω) quantified before d and ε; ∃ n0 depending on d, ε (and the other fixed parameters) with ∀ n ≥ n0; probability bounds as μ(bad) ≤ ofReal(C/n); reason: the paper's definition of its asymptotic notation; one C serves several O's because every bound is monotone in C
--   - encoding: random hashes, random probe choices, T^insertion, E[T^insertion | H_n] → uniform measure on Fin (m+1) → Fin d → Fin n times an i.i.d. uniform probe stream ℕ → Fin d consumed in order by all insertions; T^insertion : ℕ∞ (⊤ if an insertion never ends); E[· | H_n] = lintegral of the ℝ≥0∞ coercion against ProbabilityTheory.cond; reason: the probability space the paper describes (pp. 4–5); expectations of an ℕ ∪ {∞}-valued cost live in ℝ≥0∞
--   - encoding: standing assumption d ≥ D0 for a sufficiently large absolute D0 (pp. 13, 16) → ∃ D0 : ℕ, ∀ d ≥ D0; reason: the paper's 'sufficiently large absolute constant'; D0 ≥ 10^6 is implied by taking D0 larger
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 16 (PDF 17), Theorem 5.1

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Theorem 5.1 (p. 16): for `d ≥ D0` and `ε ≥ e^{−d/4}` (with `ε∗_d < ε ≤ 1`), for all `n ≥ n0(d, ε)`
there are hash-only events `H_n` with `Pr(H_nᶜ) ≤ C/n` and `E[T^insertion | H_n] ≤ C/ε`, `D0`, `C`
absolute. -/
theorem theorem_5_1 :
    ∃ D0 : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, D0 ≤ d → ∀ ε : ℝ, epsStar d < ε → ε ≤ 1 →
      Real.exp (-(d : ℝ) / 4) ≤ ε →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ∃ H : Set (Hashes (numKeys n ε + 1) d n),
          hashMeasure (numKeys n ε + 1) d n Hᶜ ≤ ENNReal.ofReal (C / n) ∧
          condExpInsertionTime (numKeys n ε) d n H ≤ ENNReal.ofReal (C / ε) := by sorry

end RWCuckoo.Threshold
