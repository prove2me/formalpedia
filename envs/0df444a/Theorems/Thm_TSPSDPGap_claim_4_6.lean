-- Prove2me | Theorems.Thm_TSPSDPGap_claim_4_6
-- name    : TSPSDPGap.claim_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:41:14.545847+00:00
-- url     : https://prove2.me/theorems/e273bc0a-40ca-4e66-b567-1fcf7c245f8f
-- title:
--   Claim 4.6 — $Y$ satisfies the zero-pattern constraint
-- statement:
--   Throughout, $g\ge2$ is even, $g\mid n$ and $g<n$ (the standing assumptions of §4), $d=n/2$, and $Y$ is the solution (3).
--   $$
--   \operatorname{trace}\bigl((I_n\otimes(J_n-I_n)+(J_n-I_n)\otimes I_n)Y\bigr)=0 .
--   $$
--   This is the third constraint of SDP (1).
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: g even, g groups of n/g vertices, a_i and b_i with denominators g, g − 1, n − g → hypotheses Even g, 2 ≤ g, g ∣ n, g < n; reason: the section's standing assumption (g even) plus the conditions under which (3) and a_i, b_i are defined; given g ∣ n they exclude only n/g ∉ ℕ, g ∈ {0, 1} and n − g = 0
--   - encoding: Y = 1/(2n)[(J_g − I_g) ⊗ J_{n/g} ⊗ B + I_g ⊗ J_{n/g} ⊗ A + I_g ⊗ I_{n/g} ⊗ (2I_n − A)] (3) → Ymat g n, entrywise: block (p, q) is (1/(2n))·2I_n if p = q, (1/(2n))A if p ≠ q lie in the same group ⌊p/(n/g)⌋, (1/(2n))B otherwise; reason: equal to (3) reindexed by Fin g × Fin (n/g) ≃ Fin n (proved: Solutions/verification/TSPSDPGap_sanity.lean, Ymat_eq_eq3); same matrix
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Claim 4.6, p.17

import Mathlib
import Definitions.Def_TSPSDPGap_Ymat
open scoped Kronecker

namespace TSPSDPGap

/-- **Claim 4.6: `Y` satisfies the zero-pattern constraint.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Claim 4.6, p.17:
"trace((I_n ⊗ (J_n − I_n) + (J_n − I_n) ⊗ I_n)Y) = 0."

**Standing hypotheses (§4, p.14).** `g` is even ("we thus assume that g is even throughout"),
`g ∣ n` ("g equally sized groups of n/g vertices"), `2 ≤ g` and `g < n` (the formulas for
`a_i, b_i` divide by `g − 1` and `n − g`; with `g ∣ n` they exclude only those undefined cases).

**Formalization Note.** `Y = Ymat g n`; `J_n` is the all-ones matrix, `I_n` is `1`. -/
theorem claim_4_6 (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    Matrix.trace (((1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ (Matrix.of (fun _ _ => (1 : ℝ)) - 1) +
      (Matrix.of (fun _ _ => (1 : ℝ)) - 1) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)) * Ymat g n) = 0 := by sorry

end TSPSDPGap
