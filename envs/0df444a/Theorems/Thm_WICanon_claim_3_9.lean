-- Prove2me | Theorems.Thm_WICanon_claim_3_9
-- name    : WICanon.claim_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:18.262192+00:00
-- url     : https://prove2.me/theorems/6f57c33b-98d1-4ffe-85f2-67a328b4f709
-- title:
--   Claim 3.9 — statistical distance from simulation
-- statement:
--   Let $X=(Z,Y)$ be a distribution over $\{0,1\}^{n_0}\times\{0,1\}^n$ and $\mathrm{Pred}$ a next-bit $\mu$-predictor for $X$. Let $\tilde Y\equiv\mathrm{Sim}^{\mathrm{Pred}}(Z,R)$ be generated on initial state $Z$ with independent uniform strings $R=(R_1,\dots,R_n)$. Then for every $i\in[n+1]$,
--
--   $$\mathrm{SD}\bigl((Z,Y_{<i}),(Z,\tilde Y_{<i})\bigr)\le 2(i-1)\mu.$$
--
--   The simulator therefore reproduces a distribution up to an error linear in the number of simulated bits.
--
--   **Formalization Note** $j=i-1$ runs over $0,\dots,n$. Footnote 10 of the paper, $\mathrm{Pred}\cdot 2^{\ell_S}\in\mathbb N$, is a hypothesis.
--
--   Differences from the source:
--   - encoding: index i ∈ [n + 1] → j = i − 1 ∈ {0, …, n}; reason: relabeling
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Claim 3.9, p.21

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_WICanon_Law
import Definitions.Def_WICanon_NextBit

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity

/-- **Claim 3.9** (statistical distance from simulation). Arnon, Mazor, Pass, Silbak, *Does Witness
Indistinguishability Require Cryptography?*, STOC 2027 submission manuscript (sha256 3f78ec3d…), p.21.
For `X = (Z, Y)` over `{0,1}^{n0} × {0,1}^n` and a next-bit `μ`-predictor `Pred` for `X`,
`SD((Z, Y_{<i}), (Z, Ỹ_{<i})) ≤ 2(i − 1)μ` for every `i ∈ [n + 1]`.

**Formalization Note.** `j = i − 1 ∈ {0, …, n}`. The no-rounding hypothesis is footnote 10, p.21. -/
theorem claim_3_9 (n0 n ℓPred ℓS : ℕ) (X : Law) (hX : IsLawOn X (n0 + n))
    (Pred : Str → Str → ℚ) (μ : ℝ) (hPred : IsNextBitPredictor X (n0 + n) ℓPred Pred μ)
    (hround : NoRounding Pred ℓPred ℓS) (j : ℕ) (hj : j ≤ n) :
    SD (prefixLaw X (n0 + j)) (prefixLaw (simJoint X n0 n Pred ℓPred ℓS) (n0 + j)) ≤
      2 * (j : ℝ) * μ := by sorry

end WICanon
