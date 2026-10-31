-- Prove2me | Theorems.Thm_TSPSDPGap_claim_4_7
-- name    : TSPSDPGap.claim_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:41:41.199329+00:00
-- url     : https://prove2.me/theorems/43034cc2-2ddb-4c37-b978-fca79eb66730
-- title:
--   Claim 4.7 — the entries of $Y$ sum to $n^2$
-- statement:
--   Throughout, $g\ge2$ is even, $g\mid n$ and $g<n$ (the standing assumptions of §4), $d=n/2$, and $Y$ is the solution (3).
--   $$
--   \operatorname{trace}(J_{n^2}Y)=n^2 .
--   $$
--   This is the fourth constraint of SDP (1).
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: g even, g groups of n/g vertices, a_i and b_i with denominators g, g − 1, n − g → hypotheses Even g, 2 ≤ g, g ∣ n, g < n; reason: the section's standing assumption (g even) plus the conditions under which (3) and a_i, b_i are defined; given g ∣ n they exclude only n/g ∉ ℕ, g ∈ {0, 1} and n − g = 0
--   - encoding: Y = 1/(2n)[(J_g − I_g) ⊗ J_{n/g} ⊗ B + I_g ⊗ J_{n/g} ⊗ A + I_g ⊗ I_{n/g} ⊗ (2I_n − A)] (3) → Ymat g n, entrywise: block (p, q) is (1/(2n))·2I_n if p = q, (1/(2n))A if p ≠ q lie in the same group ⌊p/(n/g)⌋, (1/(2n))B otherwise; reason: equal to (3) reindexed by Fin g × Fin (n/g) ≃ Fin n (proved: Solutions/verification/TSPSDPGap_sanity.lean, Ymat_eq_eq3); same matrix
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Claim 4.7, p.17

import Mathlib
import Definitions.Def_TSPSDPGap_Ymat

namespace TSPSDPGap

/-- **Claim 4.7: the entries of `Y` sum to `n²`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Claim 4.7, p.17: "trace(J_{n²}Y) = (n)²."

**Standing hypotheses (§4, p.14).** `g` is even ("we thus assume that g is even throughout"),
`g ∣ n` ("g equally sized groups of n/g vertices"), `2 ≤ g` and `g < n` (the formulas for
`a_i, b_i` divide by `g − 1` and `n − g`; with `g ∣ n` they exclude only those undefined cases).

**Formalization Note.** `Y = Ymat g n`; `J_{n²}` is the all-ones matrix on `Fin n × Fin n`. -/
theorem claim_4_7 (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    Matrix.trace (Matrix.of (fun _ _ => (1 : ℝ)) * Ymat g n) = (n : ℝ) ^ 2 := by sorry

end TSPSDPGap
