-- Prove2me | Theorems.Thm_TSPSDPGap_claim_4_5
-- name    : TSPSDPGap.claim_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:41:21.660281+00:00
-- url     : https://prove2.me/theorems/43e805e5-299a-4fe9-a777-67265d2c8af7
-- title:
--   Claim 4.5 — $Y$ satisfies the assignment constraints
-- statement:
--   Throughout, $g\ge2$ is even, $g\mid n$ and $g<n$ (the standing assumptions of §4), $d=n/2$, and $Y$ is the solution (3). For each $j=1,\dots,n$,
--   $$
--   \operatorname{trace}\bigl((I_n\otimes E_{jj})Y\bigr)=1\quad\text{and}\quad\operatorname{trace}\bigl((E_{jj}\otimes I_n)Y\bigr)=1 .
--   $$
--   These are the first two families of constraints of SDP (1).
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: g even, g groups of n/g vertices, a_i and b_i with denominators g, g − 1, n − g → hypotheses Even g, 2 ≤ g, g ∣ n, g < n; reason: the section's standing assumption (g even) plus the conditions under which (3) and a_i, b_i are defined; given g ∣ n they exclude only n/g ∉ ℕ, g ∈ {0, 1} and n − g = 0
--   - encoding: Y = 1/(2n)[(J_g − I_g) ⊗ J_{n/g} ⊗ B + I_g ⊗ J_{n/g} ⊗ A + I_g ⊗ I_{n/g} ⊗ (2I_n − A)] (3) → Ymat g n, entrywise: block (p, q) is (1/(2n))·2I_n if p = q, (1/(2n))A if p ≠ q lie in the same group ⌊p/(n/g)⌋, (1/(2n))B otherwise; reason: equal to (3) reindexed by Fin g × Fin (n/g) ≃ Fin n (proved: Solutions/verification/TSPSDPGap_sanity.lean, Ymat_eq_eq3); same matrix
--   - encoding: 1-based indices → 0-based Fin n indices; reason: Lean convention; same instances
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Claim 4.5, p.16

import Mathlib
import Definitions.Def_TSPSDPGap_Ymat
open scoped Kronecker

namespace TSPSDPGap

/-- **Claim 4.5: `Y` satisfies the assignment constraints.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Claim 4.5, p.16:
"For each j = 1, ..., n, we have trace((I_n ⊗ E_jj)Y) = 1 and trace((E_jj ⊗ I_n)Y) = 1."

**Standing hypotheses (§4, p.14).** `g` is even ("we thus assume that g is even throughout"),
`g ∣ n` ("g equally sized groups of n/g vertices"), `2 ≤ g` and `g < n` (the formulas for
`a_i, b_i` divide by `g − 1` and `n − g`; with `g ∣ n` they exclude only those undefined cases).

**Formalization Note.** `Y = Ymat g n` (equation (3)), indexed by `Fin n × Fin n` (outer =
Kronecker block index); `E_jj = Matrix.single j j 1`, `j` 0-based. -/
theorem claim_4_5 (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    (∀ j : Fin n,
      Matrix.trace (((1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ Matrix.single j j (1 : ℝ)) * Ymat g n) = 1) ∧
    (∀ j : Fin n,
      Matrix.trace ((Matrix.single j j (1 : ℝ) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)) * Ymat g n) = 1) := by sorry

end TSPSDPGap
