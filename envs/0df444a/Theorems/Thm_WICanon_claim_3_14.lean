-- Prove2me | Theorems.Thm_WICanon_claim_3_14
-- name    : WICanon.claim_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:26.354726+00:00
-- url     : https://prove2.me/theorems/cd502a70-81a1-4999-b0ec-c8f80d0232e0
-- title:
--   Claim 3.14 — conditional probabilities of close distributions
-- statement:
--   Let $Z^0,Z^1$ be distributions over $\{0,1\}^n$ with $\mathrm{SD}(Z^0,Z^1)\le\varepsilon$. For $b\in\{0,1\}$ and $i\in[n]$ let $p^b(z_{<i})=\Pr[Z^b_i=1\mid Z^b_{<i}=z_{<i}]$. Then
--
--   $$\mathop{\mathbf E}_{z_{<i}\leftarrow Z^0_{<i}}\bigl[|p^0(z_{<i})-p^1(z_{<i})|\bigr]\le 2\varepsilon.$$
--
--   Close distributions have close next-bit probabilities on average; this drives the analysis of canonical simulation.
--
--   **Formalization Note** On a null prefix $p^b=0$, the convention of Definition 3.6.
--
--   Differences from the source:
--   - encoding: index i ∈ [m] of the next bit → prefix length j = i − 1; reason: relabeling
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Claim 3.14, p.26

import Mathlib
import Definitions.Def_WICanon_Law
import Definitions.Def_WICanon_NextBit

set_option autoImplicit false

namespace WICanon

/-- **Claim 3.14** (Arnon, Mazor, Pass, Silbak, *Does Witness Indistinguishability Require
Cryptography?*, STOC 2027 submission manuscript, sha256 3f78ec3d…, p.26). If `SD(Z⁰, Z¹) ≤ ε` over
`{0,1}^n`, then `E_{z<i←Z⁰<i}[|p⁰(z_{<i}) − p¹(z_{<i})|] ≤ 2ε` for every `i ∈ [n]`.

**Formalization Note.** `j = i − 1` is the length of the prefix. A prefix that is null for `Z^b` has
`p^b = 0`, the convention of Definition 3.6. -/
theorem claim_3_14 (n : ℕ) (Z0 Z1 : Law) (h0 : IsLawOn Z0 n) (h1 : IsLawOn Z1 n) (ε : ℝ)
    (hsd : SD Z0 Z1 ≤ ε) (j : ℕ) (hj : j < n) :
    expect (prefixLaw Z0 j) (fun u => |condProb Z0 u - condProb Z1 u|) ≤ 2 * ε := by sorry

end WICanon
