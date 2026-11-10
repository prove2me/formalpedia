-- Prove2me | Theorems.Thm_SliceLinearity_Tests_lemma_6_11
-- name    : SliceLinearity.Tests.lemma_6_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:40:31.086873+00:00
-- url     : https://prove2.me/theorems/39ba7f0b-2bf8-4346-a9c2-b72e548af542
-- title:
--   Lemma 6.11 — unused coordinates remove the even-parity conditioning, uniformly in g
-- statement:
--   Fix $0<p<1$ and $k\ge3$, and let $\lambda$ be a $k$-query $p$-biased tester (on $H^{(k)}_{\rm even}$, with $\mathrm{Ber}(p)$ marginals) satisfying the sampling condition of Definition 6.7. If $|g|\le1$ ignores a block $B$ with $|B|\to\infty$, then, uniformly in $g$,
--   $$T_\lambda\Big(\frac{\mathbb 1_{H_{\rm even}}g}{\mu_p(H_{\rm even})},\dots,\frac{\mathbb 1_{H_{\rm even}}g}{\mu_p(H_{\rm even})}\Big)=2T_\lambda(g,\dots,g)+o(1),\qquad\mathbb E_{z\sim\mu_p^\circ}[g(z)]=\mathbb E_{z\sim\mu_p}[g(z)]+o(1).$$
--
--   Differences from the source:
--   - reading: o(1) as |B| → ∞, uniformly in g → one function ε : ℕ → ℝ with ε → 0, evaluated at |B|, bounding both errors for every n, B and g; reason: the strongest reading: the error depends only on |B| (the proof gives O_λ(ρ_λ^{|B|}))
--   - encoding: the §6.2 standing assumptions (0 < p < 1, k ≥ 3, λ on H^{(k)}_even with Ber(p) marginals) → hypotheses hp0, hp1, hk, IsBiasedTester p lam; reason: copied from the section preamble, p. 42
--   - generalization: the subsection assumes pn is even → the cube-only estimate holds in every dimension n, without an integrality or parity constraint on pn; reason: the proof uses product sampling and parity mixing or independent rounding, never a slice of weight pn; this includes all dimensions permitted by the subsection
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §6.2, p. 45 (PDF 47), Lemma 6.11

import Mathlib
import Definitions.Def_SliceLinearity_Tests_BiasedAnalysis
import Definitions.Def_SliceLinearity_Tests_Transfer

set_option autoImplicit false

namespace SliceLinearity.Tests

open Filter Topology in
/-- **Lemma 6.11** (Unused coordinates and parity), p. 45 (PDF 47). Fix `0 < p < 1`, `k ≥ 3` and a
`k`-query `p`-biased tester `λ` satisfying the sampling condition of Definition 6.7. If `|g| ≤ 1` ignores a
block `B` with `|B| → ∞`, then, uniformly in `g` (and `n`),
`T_λ(1_{H_even} g/μ_p(H_even), …) = 2 T_λ(g, …, g) + o(1)` and `E_{μ°_p}[g] = E_{μ_p}[g] + o(1)`. -/
theorem lemma_6_11 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (k : ℕ) (hk : 3 ≤ k)
    (lam : (Fin k → ZMod 2) → ℝ) (hlam : IsBiasedTester p lam) (hsamp : SamplingCondition lam) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ (n : ℕ) (B : Finset (Fin n)) (g : Cube n → ℝ), (∀ x, |g x| ≤ 1) → IgnoresCoords g B →
        |testAvg lam (fun _ z => (if z ∈ evenCube n then g z else 0) /
              massOn (muP p) (evenCube n)) - 2 * testAvg lam (fun _ => g)| ≤ ε B.card ∧
        |expW (muPEven p) g - expW (muP p) g| ≤ ε B.card := by sorry

end SliceLinearity.Tests
