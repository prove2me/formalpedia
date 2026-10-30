-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_unscaled_trace_square
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.unscaled_trace_square
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:00:48.252402+00:00
-- url     : https://prove2.me/theorems/657136dd-b9a5-4a5c-90a0-3503ae700952
-- title:
--   Theorem 11 / Eq.(46): exact trace square of the unscaled operator
-- statement:
--   Let integers $d,k\ge1$ and $2k\le N$ satisfy the printed range of Definition 4. Put $n=N+k$ and let $R=\sum_a W(a)$, the sum over distinct ordered ports of the unnormalized partially transposed swap words. Then
--
--   $$\operatorname{Tr}(R^2)=d^{N-k}\frac{N!}{(N-k)!}\frac{(d^2+N-1)!}{(d^2+N-k-1)!}.$$
--
--   This is Eq. (46), not the malformed factor progression in Eq. (45). The normalized-signal sum is $d^{-N}R$, so the scale must not be silently exchanged.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 10, Theorem 11 / Eq.(46): exact trace square of the unscaled operator

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.10, Theorem 11, Eq.(46): unscaled R; retain Definition 4's narrower range.
The malformed factor progression in Eq.(45) is not transcribed. -/
theorem unscaled_trace_square (d N k : ℕ) (hd : 1 ≤ d)
    (hk : 1 ≤ k) (hNk : 2*k ≤ N) :
    ((unscaledSum d N k)^2).trace =
      (d : ℂ)^(N-k) * (N.factorial : ℂ) / ((N-k).factorial : ℂ) *
        ((d^2+N-1).factorial : ℂ) / ((d^2+N-k-1).factorial : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
