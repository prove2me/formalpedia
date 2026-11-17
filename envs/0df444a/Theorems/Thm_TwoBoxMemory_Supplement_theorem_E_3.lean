-- Prove2me | Theorems.Thm_TwoBoxMemory_Supplement_theorem_E_3
-- name    : TwoBoxMemory.Supplement.theorem_E_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:16:01.498715+00:00
-- url     : https://prove2.me/theorems/b3e9d463-f752-4c8c-a538-f260e4c0a712
-- title:
--   Theorem E.3 — the strict-mixture cost domain $I(r,s)$ is open, dense and of full measure
-- statement:
--   Let $r,s\in(0,1)$ with $\log r/\log s$ irrational, and let $I(r,s)=\bigcup_{a,b\ge0}I_{ab}$ be the union of the cost intervals (E.6). Then
--
--   1. $I(r,s)$ is open;
--   2. $I(r,s)$ is dense in $(0,\infty)$: it lies in $(0,\infty)$ and its closure contains $(0,\infty)$;
--   3. $(0,\infty)\setminus I(r,s)$ has Lebesgue measure zero;
--   4. $I_{ab}\cap I_{a'b'}=\emptyset$ whenever $(a,b)\neq(a',b')$;
--   5. for every $a,b$ and costs $C,D>0$ with $C/D\in I_{ab}$, the value $V$ is finite and there is a weight $\lambda\in(0,1)$ such that the law $P_\lambda=\lambda\,\delta_{W^+}+(1-\lambda)\,\delta_{W^-}$ on the two tied greedy words satisfies
--
--   $$J_A(P_\lambda)=J_B(P_\lambda)=V;$$
--
--   this equal-risk weight is unique in $[0,1]$; and the prior $(\pi_A,\pi_B)$ of (E.7) is least favourable: $\pi_AJ_A(P)+\pi_BJ_B(P)\ge V$ for every probability law $P$ on command words;
--   6. if $r$ and $s$ are rational, $I(r,s)$ is effectively open: it is the union of the open intervals $(x_n,y_n)$ of a computable sequence of pairs of rationals.
--
--   Outside a null set of cost ratios, the optimal search law is thus a strict mixture of two words that share a finite common prefix.
--
--   Differences from the source:
--   - encoding: dense in (0, ∞) → `Icost ⊆ Ioi 0` and `Ioi 0 ⊆ closure Icost`; reason: the definition of density in a subspace
--   - encoding: complement of Lebesgue measure zero → `volume (Ioi 0 \ Icost) = 0`; reason: the complement is taken in (0, ∞), as the theorem's setting says
--   - encoding: its nonempty intervals are pairwise disjoint → `Disjoint (Iab a b) (Iab a' b')` for all (a, b) ≠ (a', b'); reason: an empty interval is disjoint from every set, so the two statements are equivalent
--   - reading: each member has a finite strict two-word saddle as in Proposition E.1 → for C, D > 0 with C/D ∈ I_ab: V < ∞, an equalizing weight λ ∈ (0, 1) on W⁺ with common risk V, uniqueness of the equal-risk weight in [0, 1], and the prior (E.7) least favourable against every probability law; reason: these are the saddle claims of Proposition E.1 (least favourable prior, unique equal-risk mixture with both weights positive, minimax); its certification sentences concern membership tests, not the saddle
--   - reading: effectively open for rational failure data → for each fixed rational (r, s), a `Computable` map ℕ → codes of rational pairs whose open intervals have union I(r, s); reason: the standard meaning of an effectively open subset of ℝ; the brief fixes the per-(r, s) reading
--   - encoding: commands A, B; risks in [0, ∞] → commands `Fin 2` with 0 = A, 1 = B; risks in `ℝ≥0∞`; reason: Lean convention; same instances
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), Theorem E.3, p.43 (PDF 45); Proposition E.1, p.42 (PDF 44); (E.1)–(E.7), pp.41–42 (PDF 43–44)

import Mathlib
import Definitions.Def_TwoBoxMemory_Risk
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Supplement_Rational
import Definitions.Def_TwoBoxMemory_Supplement_CostDomain

namespace TwoBoxMemory.Supplement

open TwoBoxMemory MeasureTheory

/-- Theorem E.3 (A dense open cost domain of full measure). For every fixed `r, s ∈ (0, 1)` with
irrational logarithmic ratio, `I(r, s) = ⋃_{a,b ≥ 0} I_ab`
1. is open;
2. is dense in `(0, ∞)` (it lies in `(0, ∞)` and its closure contains `(0, ∞)`);
3. has complement in `(0, ∞)` of Lebesgue measure zero;
4. has pairwise disjoint intervals: `I_ab ∩ I_{a'b'} = ∅` for `(a, b) ≠ (a', b')`;
5. each member has a finite strict two-word saddle as in Proposition E.1: for costs `C, D > 0`
   with `C/D ∈ I_ab`, some weight `λ ∈ (0, 1)` makes the mixture `λ δ_{W⁺} + (1 − λ) δ_{W⁻}` of the
   two tied greedy words equalize the two risks, with common value `V < ∞`; this equal-risk
   mixture weight is unique in `[0, 1]`; and the prior `(π_A, π_B)` of (E.7) is least favourable:
   `π_A J_A(P) + π_B J_B(P) ≥ V` for every probability law `P` on command words;
6. for rational failure data `r, s` the set is effectively open: it is the union of the open
   intervals of a computable sequence of pairs of rationals.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
Theorem E.3, p.43 (PDF 45); Proposition E.1, p.42 (PDF 44); (E.1)–(E.7), pp.41–42 (PDF 43–44).

**Formalization Note.** `W⁺ = wordPlus`, `W⁻ = wordMinus` (the published `greedyWord` at `β_ab`);
risks are the published `lawRisk` (in `ℝ≥0∞`) and `value` (infimum over all probability laws on
`ℕ → Fin 2`). Weights are injected with `ENNReal.ofReal`. "Minimax" for an equalizing mixture is
`J_A(P) = J_B(P) = V`. Effective openness is stated per fixed rational `(r, s)`: a `Computable`
map `ℕ → RatCode × RatCode` (each rational coded as `(n, d) ↦ n/(d+1)`) whose open intervals
have union `I(r, s)`. -/
theorem theorem_E_3 (r s : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hirr : Irrational (Real.log r / Real.log s)) :
    IsOpen (Icost r s) ∧
    Icost r s ⊆ Set.Ioi 0 ∧ Set.Ioi 0 ⊆ closure (Icost r s) ∧
    volume (Set.Ioi (0 : ℝ) \ Icost r s) = 0 ∧
    (∀ a b a' b' : ℕ, (a, b) ≠ (a', b') → Disjoint (Iab r s a b) (Iab r s a' b')) ∧
    (∀ (a b : ℕ) (C D : ℝ), 0 < C → 0 < D → C / D ∈ Iab r s a b →
      value r s C D < ⊤ ∧
      ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧
        lawRisk r s C D 0 (ENNReal.ofReal lam • Measure.dirac (wordPlus r s a b) +
            ENNReal.ofReal (1 - lam) • Measure.dirac (wordMinus r s a b)) = value r s C D ∧
        lawRisk r s C D 1 (ENNReal.ofReal lam • Measure.dirac (wordPlus r s a b) +
            ENNReal.ofReal (1 - lam) • Measure.dirac (wordMinus r s a b)) = value r s C D ∧
        (∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ 1 →
          lawRisk r s C D 0 (ENNReal.ofReal lam' • Measure.dirac (wordPlus r s a b) +
              ENNReal.ofReal (1 - lam') • Measure.dirac (wordMinus r s a b)) =
            lawRisk r s C D 1 (ENNReal.ofReal lam' • Measure.dirac (wordPlus r s a b) +
              ENNReal.ofReal (1 - lam') • Measure.dirac (wordMinus r s a b)) → lam' = lam) ∧
        (∀ P : Measure (ℕ → Fin 2), IsProbabilityMeasure P →
          value r s C D ≤ ENNReal.ofReal (piAab r s C D a b) * lawRisk r s C D 0 P +
            ENNReal.ofReal (piBab r s C D a b) * lawRisk r s C D 1 P)) ∧
    (IsRat r → IsRat s →
      ∃ f : ℕ → RatCode × RatCode, Computable f ∧
        Icost r s = ⋃ n, Set.Ioo ((f n).1.val : ℝ) ((f n).2.val : ℝ)) := by sorry

end TwoBoxMemory.Supplement
