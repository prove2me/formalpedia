-- Prove2me | Theorems.Thm_SliceLinearity_Tests_lemma_4_9
-- name    : SliceLinearity.Tests.lemma_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:37:59.298877+00:00
-- url     : https://prove2.me/theorems/c05d527a-31a3-4188-b89e-4c3d8daf1d0a
-- title:
--   Lemma 4.9 — bounded-L² approximators from a second-moment bound, with Fourier error 2ε
-- statement:
--   Let $\mu,\nu$ be distributions on a finite vector space $V$ (over a finite field $\mathbb F$), with $\mu$ of full support. Suppose that, for some $C,\varepsilon>0$ and every complex function $u$,
--   $$\|u\|_{2,\nu}^2\le C^2\|u\|_{2,\mu}^2+\varepsilon^2\|\hat u\|_{\ell_1}^2.$$
--   Then every $f$ with $|f|\le1$ has an approximator $g$, real for real $f$ over $\mathbb F_2$, satisfying
--   $$\|g\|_{2,\mu}\le C,\qquad\max_\chi|\langle f,\chi\rangle_\nu-\langle g,\chi\rangle_\mu|\le2\varepsilon.$$
--
--   Differences from the source:
--   - encoding: distributions on a finite vector space, μ of full support, characters χ → real weight functions (ν ≥ 0, μ > 0, each summing to 1) on a finite F-vector space V; characters are AddChar V ℂ; reason: finite distributions are exactly such weights; additive characters are the paper's χ_φ = ψ∘φ
--   - encoding: "real for real f over F₂" → Fintype.card F = 2 → (∀ x, (f x).im = 0) → ∀ x, (g x).im = 0; reason: a complex function is real iff its imaginary part vanishes
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §4.2, p. 26 (PDF 28), Lemma 4.9

import Mathlib
import Definitions.Def_SliceLinearity_Tests_FiniteFourier

set_option autoImplicit false

namespace SliceLinearity.Tests

/-- **Lemma 4.9** (Approximators from a second-moment bound), p. 26 (PDF 28). Let `μ, ν` be
distributions on a finite vector space `V` over a finite field `F`, with `μ` of full support. Suppose
that, for some `C, ε > 0` and every complex function `u`, `‖u‖²_{2,ν} ≤ C² ‖u‖²_{2,μ} + ε² ‖û‖²_{ℓ1}`.
Then every `|f| ≤ 1` has an approximator `g`, real for real `f` over `F₂`, with `‖g‖_{2,μ} ≤ C` and
`max_χ |⟨f, χ⟩_ν − ⟨g, χ⟩_μ| ≤ 2ε`. -/
theorem lemma_4_9 {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V] [Fintype V]
    [DecidableEq V] (μ ν : V → ℝ) (hμ : (∀ x, 0 < μ x) ∧ ∑ x, μ x = 1)
    (hν : (∀ x, 0 ≤ ν x) ∧ ∑ x, ν x = 1) (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε)
    (hmom : ∀ u : V → ℂ, normV ν u ^ 2 ≤ C ^ 2 * normV μ u ^ 2 + ε ^ 2 * fourierL1V u ^ 2)
    (f : V → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ g : V → ℂ,
      (Fintype.card F = 2 → (∀ x, (f x).im = 0) → ∀ x, (g x).im = 0) ∧
      normV μ g ≤ C ∧
      ∀ ψ : AddChar V ℂ, ‖innerV ν f (fun x => ψ x) - innerV μ g (fun x => ψ x)‖ ≤ 2 * ε := by sorry

end SliceLinearity.Tests
