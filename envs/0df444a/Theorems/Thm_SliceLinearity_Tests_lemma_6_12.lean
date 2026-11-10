-- Prove2me | Theorems.Thm_SliceLinearity_Tests_lemma_6_12
-- name    : SliceLinearity.Tests.lemma_6_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:40:16.241114+00:00
-- url     : https://prove2.me/theorems/a3094724-4287-468f-b3eb-7070b0f8a6d9
-- title:
--   Lemma 6.12 — independent rounding of a bounded function to ±1 preserves the test average and all character correlations
-- statement:
--   Fix $0<p<1$ and $k\ge3$, and let $\lambda$ be a $k$-query $p$-biased tester whose bits are pairwise independent with $\mathrm{Ber}(p)$ marginals. Every real $g$ with $|g|\le1$ has a rounding $g':\mathbb F_2^n\to\{\pm1\}$ satisfying the following bounds uniformly in $g$:
--   $$|T_\lambda(g',\dots,g')-T_\lambda(g,\dots,g)|=o(1),\qquad\max_\chi|\langle g'-g,\chi\rangle_{\mu_p}|=o(1).$$
--
--   Differences from the source:
--   - reading: o(1) uniformly in g → ε : ℕ → ℝ with ε → 0, chosen before n and g; reason: o(1) as n → ∞ with p, k, λ fixed, uniform in g
--   - encoding: the §6.2 standing assumptions (0 < p < 1, k ≥ 3, λ on H^{(k)}_even) → hypotheses hp0, hp1, hk, IsBiasedTester p lam; reason: copied from the section preamble, p. 42
--   - generalization: the subsection assumes pn is even → the cube-only estimate holds in every dimension n, without an integrality or parity constraint on pn; reason: the proof uses product sampling and parity mixing or independent rounding, never a slice of weight pn; this includes all dimensions permitted by the subsection
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §6.2, p. 46 (PDF 48), Lemma 6.12

import Mathlib
import Definitions.Def_SliceLinearity_Tests_BiasedAnalysis
import Definitions.Def_SliceLinearity_Tests_Transfer

set_option autoImplicit false

namespace SliceLinearity.Tests

open Filter Topology in
/-- **Lemma 6.12** (Rounding bounded functions), p. 46 (PDF 48). Fix `0 < p < 1`, `k ≥ 3` and a
`k`-query `p`-biased tester `λ` whose bits are pairwise independent with `Ber(p)` marginals. Every real
`|g| ≤ 1` has a rounding `g' : F₂ⁿ → {±1}` with, uniformly in `g`,
`|T_λ(g', …, g') − T_λ(g, …, g)| = o(1)` and `max_χ |⟨g' − g, χ⟩_{μ_p}| = o(1)` as `n → ∞`. -/
theorem lemma_6_12 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (k : ℕ) (hk : 3 ≤ k)
    (lam : (Fin k → ZMod 2) → ℝ) (hlam : IsBiasedTester p lam) (hpw : PairwiseIndepBits lam) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ (n : ℕ) (g : Cube n → ℝ), (∀ x, |g x| ≤ 1) →
        ∃ g' : Cube n → ℝ, (∀ x, g' x = 1 ∨ g' x = -1) ∧
          |testAvg lam (fun _ => g') - testAvg lam (fun _ => g)| ≤ ε n ∧
          ∀ ξ : Cube n, |innerW (muP p) (fun x => g' x - g x) (chi ξ)| ≤ ε n := by sorry

end SliceLinearity.Tests
