-- Prove2me | Theorems.Thm_SliceLinearity_Tests_proposition_6_17
-- name    : SliceLinearity.Tests.proposition_6_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:38:35.037447+00:00
-- url     : https://prove2.me/theorems/93afb758-7e8b-490e-8143-3a53ce7523b2
-- title:
--   Proposition 6.17 — case (ii) of the goal: the pivot test on S(r), r + 1 / 2r + 2 queries, explicit error r(r−1)/n
-- statement:
--   Let $2\le r\le n/2$. The pivot test is perfectly complete and uses $r+1$ queries for even $r$ and $2r+2$ queries for odd $r$. If $f$ passes it with probability at least $(1+\delta)/2$, then
--   $$\max_{\chi,\ \sigma\in\{\pm1\}}\mathrm{agr}_{S(r)}(f,\sigma\chi)\ge\begin{cases}\dfrac{1+\delta}2, & r\text{ even},\\[4pt]\dfrac{1+\sqrt\delta}2, & r\text{ odd}\end{cases}\;-\;\frac{r(r-1)}n.$$
--   The pivot test is also a parity test on $S(r)$: its queries lie in $S(r)$ and sum to zero (proof, p. 51).
--
--   Differences from the source:
--   - encoding: the pivot test (an (r−1)-set B and a uniform r-set S ⊆ Bᶜ, query order unspecified) → S drawn as the image of a uniform injective s : Fin r → Fin n avoiding B, queries in the order 1_S, 1_{B∪{s_j}}; for odd r two such checks concatenated; reason: the image is a uniform r-set; query order changes neither acceptance nor completeness
--   - encoding: r ≤ n/2 → 2r ≤ n; reason: same condition over ℕ
--   - encoding: "uses r + 1 (2r + 2) queries", "perfectly complete" → the weight function lives on Fin (r+1) (Fin (2r+2)) tuples, is a parity test on S(r), and accepts every linear map with probability 1; reason: the paper's definitions (p. 1, p. 2)
--   - generalization: δ with 0 < δ ≤ 1 (Definition 2.4) → δ any real (√δ is Real.sqrt, 0 for δ < 0); reason: for δ ≤ 0 the bound asks for at most 1/2 − r(r−1)/n, which a constant affine map attains; for δ > 1 the hypothesis is vacuous; the source case is included
--   - encoding: f : S → {±1}, signed characters σχ → f : F₂ⁿ → ZMod 2 (only values on the slice are queried or measured), affine maps x ↦ ⟨a,x⟩ + c, acceptance ∑ᵢ f(zᵢ) = 0; reason: σχ_ξ = (−1)^{⟨ξ,x⟩+c}; the product of ±1 answers is 1 iff the F₂ sum is 0; same instances
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §6.3, p. 51 (PDF 53), Proposition 6.17

import Mathlib
import Definitions.Def_SliceLinearity_Tests_SliceTests
import Definitions.Def_SliceLinearity_Tests_Pivot

set_option autoImplicit false

namespace SliceLinearity.Tests

/-- **Proposition 6.17** (The pivot test), p. 51 (PDF 53). Let `2 ≤ r ≤ n/2`. The pivot test is a
perfectly complete parity test on `S(r)` using `r + 1` queries for even `r` and `2r + 2` queries for odd
`r`. If `f` passes it with probability at least `(1 + δ)/2`, then
`max_{χ,σ} agr_{S(r)}(f, σχ) ≥ (1 + δ)/2 − r(r−1)/n` (`r` even), `≥ (1 + √δ)/2 − r(r−1)/n` (`r` odd). -/
theorem proposition_6_17 (n r : ℕ) (hr : 2 ≤ r) (hrn : 2 * r ≤ n) :
    (Even r →
      IsParityTestOn (slice n r) (pivotEvenW n r) ∧
      (∀ a : Cube n, accW (pivotEvenW n r) (linMap a) = 1) ∧
      ∀ (f : Cube n → ZMod 2) (δ : ℝ), (1 + δ) / 2 ≤ accW (pivotEvenW n r) f →
        (1 + δ) / 2 - (r : ℝ) * ((r : ℝ) - 1) / (n : ℝ) ≤ maxAffAgr (slice n r) f) ∧
    (Odd r →
      IsParityTestOn (slice n r) (pivotOddW n r) ∧
      (∀ a : Cube n, accW (pivotOddW n r) (linMap a) = 1) ∧
      ∀ (f : Cube n → ZMod 2) (δ : ℝ), (1 + δ) / 2 ≤ accW (pivotOddW n r) f →
        (1 + Real.sqrt δ) / 2 - (r : ℝ) * ((r : ℝ) - 1) / (n : ℝ) ≤ maxAffAgr (slice n r) f) := by sorry

end SliceLinearity.Tests
