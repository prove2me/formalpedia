-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P81_pointer_parity_classical_lower
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P81.pointer_parity_classical_lower
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:02:54.153564+00:00
-- url     : https://prove2.me/theorems/2d8e5c0d-b083-429c-9251-780171306dd0
-- title:
--   Explicit randomized pointer-parity lower bound
-- statement:
--   Let $n\ge2$, $k\ge1$, and $0\le\varepsilon<1/2$. Define $f_k$ as the XOR of all binary label bits of the endpoint after $k+1$ unrestricted alternating pointer applications from a fixed Alice vertex. Consider any public-coin protocol, with randomness independent of both inputs, that starts with Bob, uses at most $k$ messages, and outputs $f_k$ with probability at least $1-\varepsilon$ on every input. If its worst-case transmitted bit cost is at most $c$, then
--   $$
--   c\ge \frac{(1-2\varepsilon)^2 n}{2k^2}-k\log_2 n.
--   $$
--
--   The final local announcement is not charged. This retains the explicit constant and the denominator $2k^2$ of the paper's original unnumbered claim, rather than the preceding cited asymptotic bound.
-- source:
--   On rounds in quantum communication, arXiv:quant-ph/0004100v5, PDF p. 12, Original unnumbered lower bound after Definition 11

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P81

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intakethird100.P81

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Bridge50.P44 (ClassicalFirst)

/-- Original unnumbered lower bound, PDF p.12: denominator 2*k^2, not 2^(k^2).
The exact printed expression is retained with binary logarithm. -/
theorem pointer_parity_classical_lower (k n : ℕ) (hk : 0 < k) (hn : 2 ≤ n)
    (eps : ℝ) (heps : 0 ≤ eps) (hepsHalf : eps < 1 / 2) (v1 : Fin n)
    (c : ℕ) (P : PublicProtocol (PointerMap n) (PointerMap n) Bool)
    (hbound : P.bounded .bob k c) (hcorrect : P.computes (pointerParity k v1) eps) :
    (1 - 2 * eps) ^ 2 * n / (2 * (k : ℝ) ^ 2) - k * Real.logb 2 n ≤ c := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P81

end
