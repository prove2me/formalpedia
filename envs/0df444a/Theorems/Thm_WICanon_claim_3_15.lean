-- Prove2me | Theorems.Thm_WICanon_claim_3_15
-- name    : WICanon.claim_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:14.717146+00:00
-- url     : https://prove2.me/theorems/3165bc0a-9afe-4269-8b7e-db7fd4c56b99
-- title:
--   Claim 3.15 — samplers of close distributions agree
-- statement:
--   Let $Z^0,Z^1$ be distributions over $\{0,1\}^n$ with next-bit $\mu$-predictors $\mathrm{Pred}^0,\mathrm{Pred}^1$ and samplers $\mathrm{Samp}^b=\mathrm{Samp}^{\mathrm{Pred}^b}$. If $\mathrm{SD}(Z^0,Z^1)\le\varepsilon$ then for every $i\in[n]$
--
--   $$\Pr_{z_{<i}\leftarrow Z^0_{<i},\ r\leftarrow\{0,1\}^{\ell_{\mathrm{Pred}}+\ell_S}}\bigl[\mathrm{Samp}^0(z_{<i};r)\ne\mathrm{Samp}^1(z_{<i};r)\bigr]\le 3\varepsilon+4\mu.$$
--
--   On common coins the two samplers output the same bit with high probability.
--
--   **Formalization Note** The claim uses one $r$ for both samplers, so they share $\ell_{\mathrm{Pred}},\ell_S$. Footnote 10 is a hypothesis.
--
--   Differences from the source:
--   - encoding: index i ∈ [m] of the next bit → prefix length j = i − 1; reason: relabeling
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Claim 3.15, p.26

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_WICanon_Law
import Definitions.Def_WICanon_NextBit

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity QiOPoQ

open Classical in
/-- **Claim 3.15** (Arnon, Mazor, Pass, Silbak, *Does Witness Indistinguishability Require
Cryptography?*, STOC 2027 submission manuscript, sha256 3f78ec3d…, p.26). For next-bit `μ`-predictors
`Pred⁰`, `Pred¹` of `Z⁰`, `Z¹` over `{0,1}^n` with `SD(Z⁰, Z¹) ≤ ε`, and every `i ∈ [n]`,
`Pr_{z<i←Z⁰<i, r←{0,1}^{ℓPred+ℓS}}[Samp⁰(z_{<i}; r) ≠ Samp¹(z_{<i}; r)] ≤ 3ε + 4μ`.

**Formalization Note.** The claim uses one `r` for both samplers, so the predictors share `ℓPred` and
`ℓS`. The no-rounding hypotheses are footnote 10, p.21. `j = i − 1`. -/
theorem claim_3_15 (n ℓPred ℓS : ℕ) (Z0 Z1 : Law) (h0 : IsLawOn Z0 n) (h1 : IsLawOn Z1 n)
    (Pred0 Pred1 : Str → Str → ℚ) (μ ε : ℝ)
    (hP0 : IsNextBitPredictor Z0 n ℓPred Pred0 μ) (hP1 : IsNextBitPredictor Z1 n ℓPred Pred1 μ)
    (hr0 : NoRounding Pred0 ℓPred ℓS) (hr1 : NoRounding Pred1 ℓPred ℓS)
    (hsd : SD Z0 Z1 ≤ ε) (j : ℕ) (hj : j < n) :
    (expect (prefixLaw Z0 j) fun u => avgCoins (ℓPred + ℓS) fun r =>
      if samp Pred0 ℓPred ℓS u r ≠ samp Pred1 ℓPred ℓS u r then 1 else 0) ≤ 3 * ε + 4 * μ := by sorry

end WICanon
