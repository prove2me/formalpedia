-- Prove2me | Theorems.Thm_SliceLinearity_Tests_fact_5_3
-- name    : SliceLinearity.Tests.fact_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:37:58.818193+00:00
-- url     : https://prove2.me/theorems/8adc748e-54f0-4a76-bf86-04f17d9763a9
-- title:
--   Fact 5.3 — Hölder for fractional covers (Finner, Friedgut)
-- statement:
--   Let $I_1,\dots,I_m\subseteq[n]$ be such that every coordinate lies in at least two of them. For functions $a_j:\mathbb F_2^{I_j}\to\mathbb C$,
--   $$\sum_{u\in\mathbb F_2^n}\prod_{j=1}^m|a_j(u|_{I_j})|\le\prod_{j=1}^m\Big(\sum_{v\in\mathbb F_2^{I_j}}|a_j(v)|^2\Big)^{1/2}.$$
--
--   Differences from the source:
--   - encoding: F₂^{I_j} and u|_{I_j} → functions ↥(I j) → ZMod 2 and fun i => u i; reason: same objects
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §5.1, p. 31 (PDF 33), Fact 5.3

import Mathlib
import Definitions.Def_SliceLinearity_Tests_SliceTests

set_option autoImplicit false

namespace SliceLinearity.Tests

/-- **Fact 5.3** (Hölder for fractional covers), p. 31 (PDF 33). Let `I₁, …, I_m ⊆ [n]` be such that
every coordinate lies in at least two of them. For functions `a_j : F₂^{I_j} → ℂ`,
`∑_{u ∈ F₂ⁿ} ∏_j |a_j(u|_{I_j})| ≤ ∏_j (∑_{v ∈ F₂^{I_j}} |a_j(v)|²)^{1/2}`. -/
theorem fact_5_3 {n m : ℕ} (I : Fin m → Finset (Fin n))
    (hI : ∀ i : Fin n, 2 ≤ (Finset.univ.filter fun j => i ∈ I j).card)
    (a : (j : Fin m) → (↥(I j) → ZMod 2) → ℂ) :
    ∑ u : Cube n, ∏ j, ‖a j (fun i => u i)‖ ≤ ∏ j, Real.sqrt (∑ v, ‖a j v‖ ^ 2) := by sorry

end SliceLinearity.Tests
