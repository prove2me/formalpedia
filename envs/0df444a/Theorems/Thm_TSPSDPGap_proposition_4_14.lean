-- Prove2me | Theorems.Thm_TSPSDPGap_proposition_4_14
-- name    : TSPSDPGap.proposition_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:41:43.759056+00:00
-- url     : https://prove2.me/theorems/db6df4b4-ab2b-4892-bb45-9413cb1088de
-- title:
--   Proposition 4.14 — $Y\succeq0$
-- statement:
--   Throughout, $g\ge2$ is even, $g\mid n$ and $g<n$ (the standing assumptions of §4), $d=n/2$, and $Y$ is the solution (3).
--   $$
--   Y\succeq0 .
--   $$
--   This is the semidefinite constraint of SDP (1), the last ingredient of feasibility (Proposition 4.4).
--
--   **Formalization Note** $Y\succeq0$ is `Matrix.PosSemidef` (symmetric with nonnegative quadratic form).
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: g even, g groups of n/g vertices, a_i and b_i with denominators g, g − 1, n − g → hypotheses Even g, 2 ≤ g, g ∣ n, g < n; reason: the section's standing assumption (g even) plus the conditions under which (3) and a_i, b_i are defined; given g ∣ n they exclude only n/g ∉ ℕ, g ∈ {0, 1} and n − g = 0
--   - encoding: Y = 1/(2n)[(J_g − I_g) ⊗ J_{n/g} ⊗ B + I_g ⊗ J_{n/g} ⊗ A + I_g ⊗ I_{n/g} ⊗ (2I_n − A)] (3) → Ymat g n, entrywise: block (p, q) is (1/(2n))·2I_n if p = q, (1/(2n))A if p ≠ q lie in the same group ⌊p/(n/g)⌋, (1/(2n))B otherwise; reason: equal to (3) reindexed by Fin g × Fin (n/g) ≃ Fin n (proved: Solutions/verification/TSPSDPGap_sanity.lean, Ymat_eq_eq3); same matrix
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Proposition 4.14, p.21 (proof pp.21–26)

import Mathlib
import Definitions.Def_TSPSDPGap_Ymat

namespace TSPSDPGap

/-- **Proposition 4.14: `Y ⪰ 0`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Proposition 4.14, p.21: "Y ⪰ 0."

**Standing hypotheses (§4, p.14).** `g` is even ("we thus assume that g is even throughout"),
`g ∣ n` ("g equally sized groups of n/g vertices"), `2 ≤ g` and `g < n` (the formulas for
`a_i, b_i` divide by `g − 1` and `n − g`; with `g ∣ n` they exclude only those undefined cases).

**Formalization Note.** `Y = Ymat g n`; `⪰ 0` is `Matrix.PosSemidef` (symmetric with
nonnegative quadratic form). -/
theorem proposition_4_14 (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    (Ymat g n).PosSemidef := by sorry

end TSPSDPGap
