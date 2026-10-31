-- Prove2me | Theorems.Thm_TSPSDPGap_lemma_4_10
-- name    : TSPSDPGap.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:14.876119+00:00
-- url     : https://prove2.me/theorems/18d4acfb-7e5b-4220-85b1-be0812d5d9c5
-- title:
--   Lemma 4.10 — $\sum_{i=1}^d a_i=1$
-- statement:
--   Throughout, $g\ge2$ is even, $g\mid n$ and $g<n$ (the standing assumptions of §4), $d=n/2$, and $Y$ is the solution (3).
--   $$
--   \sum_{i=1}^{d}a_i=1 .
--   $$
--   It makes each block $\frac1{2n}A$ of $Y$ sum to $1$ (Claim 4.7) and gives $a^{(0)}=1$.
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: g even, g groups of n/g vertices, a_i and b_i with denominators g, g − 1, n − g → hypotheses Even g, 2 ≤ g, g ∣ n, g < n; reason: the section's standing assumption (g even) plus the conditions under which (3) and a_i, b_i are defined; given g ∣ n they exclude only n/g ∉ ℕ, g ∈ {0, 1} and n − g = 0
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Lemma 4.10, p.18

import Mathlib
import Definitions.Def_TSPSDPGap_coeffA

namespace TSPSDPGap

/-- **Lemma 4.10: `Σ_{i=1}^d a_i = 1`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Lemma 4.10, p.18: "Σ_{i=1}^d a_i = 1."

**Standing hypotheses (§4, p.14).** `g` is even ("we thus assume that g is even throughout"),
`g ∣ n` ("g equally sized groups of n/g vertices"), `2 ≤ g` and `g < n` (the formulas for
`a_i, b_i` divide by `g − 1` and `n − g`; with `g ∣ n` they exclude only those undefined cases).

**Formalization Note.** `a_i = coeffA g n i`, `d = n / 2`. -/
theorem lemma_4_10 (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    ∑ i ∈ Finset.Icc 1 (n / 2), coeffA g n i = 1 := by sorry

end TSPSDPGap
