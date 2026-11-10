-- Prove2me | Theorems.Thm_SliceLinearity_Tests_lemma_6_13
-- name    : SliceLinearity.Tests.lemma_6_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:40:39.991685+00:00
-- url     : https://prove2.me/theorems/8067960d-c42c-46d1-89b8-633abba0dc37
-- title:
--   Lemma 6.13 — the symmetric active-set test satisfies the transfer conditions with C = 1
-- statement:
--   Let $m\ge3$ and $1/m\le p\le1/(m-1)$, or $m=2$ and $p=1/2$ (the BLR test), and $k=m+1$. The symmetric active-set test satisfies Definition 6.7 with $C=1$. That is, under $\lambda_{p,k}$ the bits are pairwise independent, and the zero vector and every weight-two vector have positive probability. Moreover, for arbitrary real functions $h_1,\dots,h_k$ and every $i\in[k]$,
--   $$|T_{\lambda_{p,k}}(h_1,\dots,h_k)|\le\max_\chi|\langle h_i,\chi\rangle_{\mu_p}|\cdot\prod_{j\ne i}\|h_j\|_{2,\mu_p}.$$
--
--   Differences from the source:
--   - encoding: the symmetric active-set test → lambdaPK p m with (3 ≤ m ∧ 1/m ≤ p ≤ 1/(m−1)) ∨ (m = 2 ∧ p = 1/2); reason: the setting fixed on p. 47 (PDF 49) together with the BLR case allowed on p. 48 (PDF 50)
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §6.2.1, p. 48 (PDF 50), Lemma 6.13

import Mathlib
import Definitions.Def_SliceLinearity_Tests_ActiveSet
import Definitions.Def_SliceLinearity_Tests_Transfer

set_option autoImplicit false

namespace SliceLinearity.Tests

/-- **Lemma 6.13** (Transfer conditions for the symmetric active-set test), p. 48 (PDF 50). For
`m ≥ 3`, `1/m ≤ p ≤ 1/(m − 1)` (and for the BLR case `m = 2`, `p = 1/2`), the symmetric active-set test
`λ_{p,k}`, `k = m + 1`, satisfies Definition 6.7 with `C = 1`: the bits are pairwise independent, the
zero vector and every weight-two vector have positive probability, and for arbitrary real
`h₁, …, h_k` and every `i`, `|T_{λ_{p,k}}(h)| ≤ max_χ |⟨hᵢ, χ⟩_{μ_p}| · ∏_{j≠i} ‖h_j‖_{2,μ_p}`. -/
theorem lemma_6_13 (m : ℕ) (p : ℝ)
    (hmp : (3 ≤ m ∧ 1 / (m : ℝ) ≤ p ∧ p ≤ 1 / ((m : ℝ) - 1)) ∨ (m = 2 ∧ p = 1 / 2)) :
    SamplingCondition (lambdaPK p m) ∧ MultilinearEstimate p (lambdaPK p m) 1 := by sorry

end SliceLinearity.Tests
