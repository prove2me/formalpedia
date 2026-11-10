-- Prove2me | Theorems.Thm_StableCountSub3_lemma_4_5
-- name    : StableCountSub3.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:51:41.089195+00:00
-- url     : https://prove2.me/theorems/a18a524c-3b08-4765-8d5a-371d19aca69d
-- title:
--   Lemma 4.5 — savings from support sizes, and their additivity
-- statement:
--   Fix a downset $D$, a man $m$ and a positive integer $d$; $E_U[\log N_m(D,U)\mid D]$ is over all priorities, including $U_m$, with $D$ fixed.
--   (1) If $s^\pm_{m,D}(d)\ge d+2$ in either direction, $E_U[\log N_m(D,U)\mid D]\le C_0-\delta_d$.
--   (2) If $s^\pm_{m,D}(d)\ge d+3$ in either direction, $E_U[\log N_m(D,U)\mid D]\le C_0-\bigl(1+\frac{d+1}{d+4}\bigr)\delta_d$.
--   (3) For any finite set $P$ of distinct direction–depth pairs $(\pm,d')$, $d'\ge1$, each with $s^\pm_{m,D}(d')\ge d'+2$, $E_U[\log N_m(D,U)\mid D]\le C_0-\sum_{(\pm,d')\in P}\mathrm{sav}(\pm,d')$, where $\mathrm{sav}(\pm,d')$ is $(1+\frac{d'+1}{d'+4})\delta_{d'}$ if $s^\pm_{m,D}(d')\ge d'+3$ and $\delta_{d'}$ otherwise (only the stronger saving, once).
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: s^±_{m,D}(k) = ∞ and undefined cones/supports when the k-th rotation does not exist → ssize : ℕ∞ with ⊤ for ∞; principalCone and supp are Option-valued (none = undefined); reason: Lean convention; comparisons such as s ≥ d+2 are true at ⊤, as the paper uses them
--   - encoding: E_U[log N_m(D,U) | D]; "the savings from any finite collection of such pairs may be summed, and the total subtracted from C0" → expLogN = ∫ log N_m(D,U) d(unifCube n); a Finset P of (direction, depth) pairs with savingAt; reason: the expectation written out; a finite collection of distinct pairs is a finset
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Lemma 4.5, p. 23 (PDF 25)

import Mathlib
import Definitions.Def_StableCountSub3_Savings

open StableMatching

namespace StableCountSub3

/-- Lemma 4.5 (savings from support sizes), all three clauses. -/
theorem lemma_4_5 {n : ℕ} (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D)
    (m : Fin n) (d : ℕ) (hd : 1 ≤ d) :
    ((∃ dir, ((d + 2 : ℕ) : ℕ∞) ≤ ssize I D m dir d) →
      expLogN I D m ≤ C0 - delta d) ∧
    ((∃ dir, ((d + 3 : ℕ) : ℕ∞) ≤ ssize I D m dir d) →
      expLogN I D m ≤ C0 - (1 + ((d : ℝ) + 1) / ((d : ℝ) + 4)) * delta d) ∧
    -- savings over any finite collection of distinct direction–depth pairs add, each pair
    -- contributing only its stronger saving, once
    (∀ P : Finset (Dir × ℕ),
      (∀ p ∈ P, 1 ≤ p.2 ∧ ((p.2 + 2 : ℕ) : ℕ∞) ≤ ssize I D m p.1 p.2) →
      expLogN I D m ≤ C0 - ∑ p ∈ P, savingAt I D m p.1 p.2) := by sorry

end StableCountSub3
