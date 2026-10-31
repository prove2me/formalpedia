-- Prove2me | Theorems.Thm_TSPSDPGap_claim_4_17
-- name    : TSPSDPGap.claim_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:44.690125+00:00
-- url     : https://prove2.me/theorems/1e84feed-9d9c-43f1-9fa9-7e06ed7fc177
-- title:
--   Claim 4.17 — $b^{(k)}$ in terms of $a^{(k)}$
-- statement:
--   Throughout, $g\ge2$ is even, $g\mid n$ and $g<n$ (the standing assumptions of §4), $d=n/2$, and $Y$ is the solution (3). For $k=1,\dots,n-1$,
--   $$
--   b^{(k)}=-\frac{g}{n(g-1)}-\frac{n-g}{n(g-1)}\,a^{(k)} .
--   $$
--   It reduces the eigenvalues of $2nY$ to expressions in $a^{(k)}$ alone (Claim 4.18).
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: g even, g groups of n/g vertices, a_i and b_i with denominators g, g − 1, n − g → hypotheses Even g, 2 ≤ g, g ∣ n, g < n; reason: the section's standing assumption (g even) plus the conditions under which (3) and a_i, b_i are defined; given g ∣ n they exclude only n/g ∉ ℕ, g ∈ {0, 1} and n − g = 0
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Claim 4.17, p.22

import Mathlib
import Definitions.Def_TSPSDPGap_aHat
import Definitions.Def_TSPSDPGap_bHat

namespace TSPSDPGap

/-- **Claim 4.17: `b^(k)` in terms of `a^(k)`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Claim 4.17, p.22:
"For k = 1, ..., n − 1, b^(k) = − g/(n(g − 1)) − (n − g)/(n(g − 1)) a^(k)."

**Standing hypotheses (§4, p.14).** `g` is even ("we thus assume that g is even throughout"),
`g ∣ n` ("g equally sized groups of n/g vertices"), `2 ≤ g` and `g < n` (the formulas for
`a_i, b_i` divide by `g − 1` and `n − g`; with `g ∣ n` they exclude only those undefined cases).

**Formalization Note.** `k : ℕ` with `1 ≤ k < n`; real arithmetic. -/
theorem claim_4_17 (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) :
    bHat g n k = -((g : ℝ) / ((n : ℝ) * ((g : ℝ) - 1))) -
      ((n : ℝ) - g) / ((n : ℝ) * ((g : ℝ) - 1)) * aHat g n k := by sorry

end TSPSDPGap
