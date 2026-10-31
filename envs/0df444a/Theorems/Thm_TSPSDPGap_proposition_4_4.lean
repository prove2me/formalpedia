-- Prove2me | Theorems.Thm_TSPSDPGap_proposition_4_4
-- name    : TSPSDPGap.proposition_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:41:29.11231+00:00
-- url     : https://prove2.me/theorems/e5fe64c5-8c9a-466c-932c-ddd2b45dc72b
-- title:
--   Proposition 4.4 — $Y$ is feasible for SDP (1)
-- statement:
--   Throughout, $g\ge2$ is even, $g\mid n$ and $g<n$ (the standing assumptions of §4), $d=n/2$, and $Y$ is the solution (3). Then $Y$ satisfies every constraint of SDP (1): both assignment families, the zero-pattern constraint, $\operatorname{trace}(J_{n^2}Y)=n^2$, $Y\ge0$, symmetry and $Y\succeq0$.
--
--   Since SDPs (1) and (2) have the same constraints up to dimension, $Y$ is also feasible for SDP (2) on $n+1$ vertices.
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: g even, g groups of n/g vertices, a_i and b_i with denominators g, g − 1, n − g → hypotheses Even g, 2 ≤ g, g ∣ n, g < n; reason: the section's standing assumption (g even) plus the conditions under which (3) and a_i, b_i are defined; given g ∣ n they exclude only n/g ∉ ℕ, g ∈ {0, 1} and n − g = 0
--   - encoding: Y = 1/(2n)[(J_g − I_g) ⊗ J_{n/g} ⊗ B + I_g ⊗ J_{n/g} ⊗ A + I_g ⊗ I_{n/g} ⊗ (2I_n − A)] (3) → Ymat g n, entrywise: block (p, q) is (1/(2n))·2I_n if p = q, (1/(2n))A if p ≠ q lie in the same group ⌊p/(n/g)⌋, (1/(2n))B otherwise; reason: equal to (3) reindexed by Fin g × Fin (n/g) ≃ Fin n (proved: Solutions/verification/TSPSDPGap_sanity.lean, Ymat_eq_eq3); same matrix
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Proposition 4.4, p.16

import Mathlib
import Definitions.Def_TSPSDPGap_IsSDP1Feasible
import Definitions.Def_TSPSDPGap_Ymat

namespace TSPSDPGap

/-- **Proposition 4.4: `Y` is feasible for SDP (1).**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Proposition 4.4, p.16: "Y, as given by Equation (3), is feasible for SDP (1)."

**Standing hypotheses (§4, p.14).** `g` is even ("we thus assume that g is even throughout"),
`g ∣ n` ("g equally sized groups of n/g vertices"), `2 ≤ g` and `g < n` (the formulas for
`a_i, b_i` divide by `g − 1` and `n − g`; with `g ∣ n` they exclude only those undefined cases).

**Formalization Note.** `Y = Ymat g n`; feasibility is `IsSDP1Feasible n` (all constraints of
SDP (1), p.6, which are also those of SDP (2) on `n + 1` vertices). -/
theorem proposition_4_4 (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    IsSDP1Feasible n (Ymat g n) := by sorry

end TSPSDPGap
