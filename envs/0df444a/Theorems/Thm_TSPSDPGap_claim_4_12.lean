-- Prove2me | Theorems.Thm_TSPSDPGap_claim_4_12
-- name    : TSPSDPGap.claim_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:41:10.268307+00:00
-- url     : https://prove2.me/theorems/500f908c-5abc-450c-936b-949c12f728fa
-- title:
--   Claim 4.12 — $Y\ge0$ (with $a_i\ge0$, $b_i\ge0$)
-- statement:
--   Throughout, $g\ge2$ is even, $g\mid n$ and $g<n$ (the standing assumptions of §4), $d=n/2$, and $Y$ is the solution (3). Then
--
--   1. $a_i\ge0$ for $i=1,\dots,d$;
--   2. $b_i\ge0$ for $i=1,\dots,d$;
--   3. $Y\ge0$ entrywise.
--
--   The paper's claim is item 3; its proof consists of items 1 and 2, which Proposition 4.14 uses again.
--
--   Differences from the source:
--   - generalization: Y ≥ 0 → a_i ≥ 0 and b_i ≥ 0 for 1 ≤ i ≤ d, and Y ≥ 0; reason: the extra conjuncts are what the claim's proof establishes (pp.20–21) and are reused on p.25; dropping them gives the printed claim
--   - encoding: standing assumptions of §4: g even, g groups of n/g vertices, a_i and b_i with denominators g, g − 1, n − g → hypotheses Even g, 2 ≤ g, g ∣ n, g < n; reason: the section's standing assumption (g even) plus the conditions under which (3) and a_i, b_i are defined; given g ∣ n they exclude only n/g ∉ ℕ, g ∈ {0, 1} and n − g = 0
--   - encoding: Y = 1/(2n)[(J_g − I_g) ⊗ J_{n/g} ⊗ B + I_g ⊗ J_{n/g} ⊗ A + I_g ⊗ I_{n/g} ⊗ (2I_n − A)] (3) → Ymat g n, entrywise: block (p, q) is (1/(2n))·2I_n if p = q, (1/(2n))A if p ≠ q lie in the same group ⌊p/(n/g)⌋, (1/(2n))B otherwise; reason: equal to (3) reindexed by Fin g × Fin (n/g) ≃ Fin n (proved: Solutions/verification/TSPSDPGap_sanity.lean, Ymat_eq_eq3); same matrix
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Claim 4.12, p.19 (proof pp.20–21)

import Mathlib
import Definitions.Def_TSPSDPGap_Ymat

namespace TSPSDPGap

/-- **Claim 4.12: `Y ≥ 0`, together with `a_i ≥ 0` and `b_i ≥ 0`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Claim 4.12, p.19: "Y ≥ 0." Its proof (p.19): "To show that Y ≥ 0, we show that the a_i
and b_i are nonnegative", carried out for `i = 1, …, d` on pp.20–21.

**Standing hypotheses (§4, p.14).** `g` is even ("we thus assume that g is even throughout"),
`g ∣ n` ("g equally sized groups of n/g vertices"), `2 ≤ g` and `g < n` (the formulas for
`a_i, b_i` divide by `g − 1` and `n − g`; with `g ∣ n` they exclude only those undefined cases).

The statement is the conjunction: `a_i ≥ 0` and `b_i ≥ 0` for `1 ≤ i ≤ d`, and every entry of
`Y` is nonnegative.

**Formalization Note.** `a_i = coeffA g n i`, `b_i = coeffB g n i`, `d = n / 2`, `Y = Ymat g n`.
The first two conjuncts are proved in the claim's proof and reused in Proposition 4.14 (p.25). -/
theorem claim_4_12 (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    (∀ i ∈ Finset.Icc 1 (n / 2), 0 ≤ coeffA g n i) ∧
    (∀ i ∈ Finset.Icc 1 (n / 2), 0 ≤ coeffB g n i) ∧
    ∀ a b, 0 ≤ Ymat g n a b := by sorry

end TSPSDPGap
