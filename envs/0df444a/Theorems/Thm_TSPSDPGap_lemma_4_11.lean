-- Prove2me | Theorems.Thm_TSPSDPGap_lemma_4_11
-- name    : TSPSDPGap.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:18.041109+00:00
-- url     : https://prove2.me/theorems/fe89ec79-807e-42f4-b7b2-60569e5d4155
-- title:
--   Lemma 4.11 — $\sum_{i=1}^d b_i=1$
-- statement:
--   Throughout, $g\ge2$ is even, $g\mid n$ and $g<n$ (the standing assumptions of §4), $d=n/2$, and $Y$ is the solution (3).
--   $$
--   \sum_{i=1}^{d}b_i=1 .
--   $$
--   It makes each block $\frac1{2n}B$ of $Y$ sum to $1$ (Claim 4.7) and gives $b^{(0)}=1$.
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: g even, g groups of n/g vertices, a_i and b_i with denominators g, g − 1, n − g → hypotheses Even g, 2 ≤ g, g ∣ n, g < n; reason: the section's standing assumption (g even) plus the conditions under which (3) and a_i, b_i are defined; given g ∣ n they exclude only n/g ∉ ℕ, g ∈ {0, 1} and n − g = 0
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Lemma 4.11, p.18

import Mathlib
import Definitions.Def_TSPSDPGap_coeffB

namespace TSPSDPGap

/-- **Lemma 4.11: `Σ_{i=1}^d b_i = 1`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Lemma 4.11, p.18: "Σ_{i=1}^d b_i = 1."

**Standing hypotheses (§4, p.14).** `g` is even ("we thus assume that g is even throughout"),
`g ∣ n` ("g equally sized groups of n/g vertices"), `2 ≤ g` and `g < n` (the formulas for
`a_i, b_i` divide by `g − 1` and `n − g`; with `g ∣ n` they exclude only those undefined cases).

**Formalization Note.** `b_i = coeffB g n i`, `d = n / 2`. -/
theorem lemma_4_11 (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    ∑ i ∈ Finset.Icc 1 (n / 2), coeffB g n i = 1 := by sorry

end TSPSDPGap
