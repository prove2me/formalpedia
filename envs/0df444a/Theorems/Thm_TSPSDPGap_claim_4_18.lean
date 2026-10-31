-- Prove2me | Theorems.Thm_TSPSDPGap_claim_4_18
-- name    : TSPSDPGap.claim_4_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:41:34.318906+00:00
-- url     : https://prove2.me/theorems/76719413-d301-467b-bf64-d8d465fa2db8
-- title:
--   Claim 4.18 — the eigenvalues of $2nY$
-- statement:
--   Throughout, $g\ge2$ is even, $g\mid n$ and $g<n$ (the standing assumptions of §4), $d=n/2$, and $Y$ is the solution (3). The set of eigenvalues of $2nY$ is
--   $$
--   \{0,\,2n\}\ \cup\ \Bigl\{\,2\frac{g}{g-1}+2\frac{n-g}{g-1}\,a^{(k)}\ :\ 1\le k\le n-1\Bigr\}\ \cup\ \bigl\{\,2-2a^{(k)}\ :\ 1\le k\le n-1\bigr\},
--   $$
--   where $2n$ and $0$ come from $k=0$ and $0$ also from every $k\ge1$.
--
--   Positive semidefiniteness of $Y$ (Proposition 4.14) follows by showing these values are nonnegative.
--
--   Differences from the source:
--   - reading: the eigenvalues of 2nY are the listed values → the real spectrum of 2nY equals the set of listed values; reason: the claim lists values, not multiplicities (0 is listed twice)
--   - encoding: standing assumptions of §4: g even, g groups of n/g vertices, a_i and b_i with denominators g, g − 1, n − g → hypotheses Even g, 2 ≤ g, g ∣ n, g < n; reason: the section's standing assumption (g even) plus the conditions under which (3) and a_i, b_i are defined; given g ∣ n they exclude only n/g ∉ ℕ, g ∈ {0, 1} and n − g = 0
--   - encoding: Y = 1/(2n)[(J_g − I_g) ⊗ J_{n/g} ⊗ B + I_g ⊗ J_{n/g} ⊗ A + I_g ⊗ I_{n/g} ⊗ (2I_n − A)] (3) → Ymat g n, entrywise: block (p, q) is (1/(2n))·2I_n if p = q, (1/(2n))A if p ≠ q lie in the same group ⌊p/(n/g)⌋, (1/(2n))B otherwise; reason: equal to (3) reindexed by Fin g × Fin (n/g) ≃ Fin n (proved: Solutions/verification/TSPSDPGap_sanity.lean, Ymat_eq_eq3); same matrix
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Claim 4.18, p.23

import Mathlib
import Definitions.Def_TSPSDPGap_Ymat
import Definitions.Def_TSPSDPGap_aHat

namespace TSPSDPGap

/-- **Claim 4.18: the eigenvalues of `2nY`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Claim 4.18, p.23:
"The eigenvalues of 2nY are 0, 2(g/(g−1)) + 2((n−g)/(g−1)) a^(k), 2 − 2a^(k), over
k = 1, ..., n − 1 and 2n, 0, corresponding to k = 0."

**Standing hypotheses (§4, p.14).** `g` is even ("we thus assume that g is even throughout"),
`g ∣ n` ("g equally sized groups of n/g vertices"), `2 ≤ g` and `g < n` (the formulas for
`a_i, b_i` divide by `g − 1` and `n − g`; with `g ∣ n` they exclude only those undefined cases).

The statement: the set of eigenvalues of `2nY` is exactly
`{0, 2n} ∪ {2g/(g−1) + 2(n−g)/(g−1)·a^(k) : 1 ≤ k ≤ n−1} ∪ {2 − 2a^(k) : 1 ≤ k ≤ n−1}`.

**Formalization Note.** `Y = Ymat g n`; eigenvalues as a set (no multiplicities), i.e.
`spectrum ℝ`; `k : ℕ` with `1 ≤ k < n`. -/
theorem claim_4_18 (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    spectrum ℝ ((2 * (n : ℝ)) • Ymat g n) =
      ({0, 2 * (n : ℝ)} : Set ℝ) ∪
      {x | ∃ k : ℕ, 1 ≤ k ∧ k < n ∧
        x = 2 * ((g : ℝ) / ((g : ℝ) - 1)) + 2 * (((n : ℝ) - g) / ((g : ℝ) - 1)) * aHat g n k} ∪
      {x | ∃ k : ℕ, 1 ≤ k ∧ k < n ∧ x = 2 - 2 * aHat g n k} := by sorry

end TSPSDPGap
