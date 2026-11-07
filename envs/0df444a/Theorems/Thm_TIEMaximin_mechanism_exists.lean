-- Prove2me | Theorems.Thm_TIEMaximin_mechanism_exists
-- name    : TIEMaximin.mechanism_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:48:05.800975+00:00
-- url     : https://prove2.me/theorems/08c7ccec-dbdc-41f8-856a-bdabc8750a33
-- title:
--   §4.4 — the mechanism is well defined
-- statement:
--   Let $m\ge n\ge2$ and let $v$ be a nonnegative profile. A lottery of the mechanism of §4.4 exists at $v$. For every order of $D$ by decreasing $1/k_i$ and every 0–1 point of (12), the matrix $b$ is a fractional suballocation (requirement (R2)), and its entries strictly between zero and one equal $1/k_i$ in row $i$, so that Lemma 4.3 applies.
--
--   Together with Propositions 5.1 and 5.3, which hold for every lottery of the mechanism, this shows that the mechanism of §4.4 exists at every profile and has both properties.
--
--   Differences from the source:
--   - reading: the lottery of the mechanism (§4.4) → every `L` with `IsMechLottery v L`: any order of D with k nondecreasing, any lotteries with the properties of Lemmas 4.1 and 4.3, any completion with the conditional probabilities e_ig/e_g; reason: §4.4 fixes these only through their properties, and Lemma 4.4's proof allows any such joint distribution; `mechanism_exists` states that such an L exists
--   - reading: α (Sections 3 and 4) → α = 1/6; reason: Table 2: "α = 1/6 in this paper"; §4.4 prepares Theorem 1.1
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §4.4, p.22

import Mathlib
import Definitions.Def_TIEMaximin_MechLottery

namespace TIEMaximin

/-- **§4.4, the mechanism is well defined** (p.22). At every nonnegative profile the four steps can be
carried out: a lottery `L` with `IsMechLottery v L` exists. For every 0–1 point of (12), `b` is a
fractional suballocation (requirement (R2)) and the fractional entries of row `i` lie on the
`1/k_i` grid, so that Lemma 4.3 applies.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, §4.4, p.22: "By (14), these fractions
fit on every unreserved good, and a reserved good has only its owner, so b is indeed a fractional
suballocation; this is requirement (R2). Third, it rounds b: the fractional entries of row i lie
on the 1/k_i grid, so Lemma 4.3 applies".

**Formalization Note.** This is what makes `proposition_5_1`, `corollary_5_2` and
`proposition_5_3` non-vacuous. -/
theorem mechanism_exists {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (v : Fin n → Fin m → ℝ) (hv : Nonneg v) :
    (∃ L : PMF (Alloc n m), IsMechLottery v L) ∧
    ∀ (ord : List (Fin n)) (pt : ResPt n m), IsDOrder (1 / 6) v ord →
      IsResPoint (1 / 6) v ord pt →
      (∀ i g, 0 ≤ bComp (1 / 6) v pt i g ∧ bComp (1 / 6) v pt i g ≤ 1) ∧
      (∀ g, ∑ i, bComp (1 / 6) v pt i g ≤ 1) ∧
      ∀ i g, 0 < bComp (1 / 6) v pt i g → bComp (1 / 6) v pt i g < 1 →
        bComp (1 / 6) v pt i g = 1 / (kDef (1 / 6) v i : ℝ) := by sorry

end TIEMaximin
