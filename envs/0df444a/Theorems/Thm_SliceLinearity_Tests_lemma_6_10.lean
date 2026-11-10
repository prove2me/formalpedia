-- Prove2me | Theorems.Thm_SliceLinearity_Tests_lemma_6_10
-- name    : SliceLinearity.Tests.lemma_6_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:38:44.216173+00:00
-- url     : https://prove2.me/theorems/a495d21a-65f1-4043-a3a3-0330b8413ead
-- title:
--   Lemma 6.10 — slice vs even-weight biased cube: Fourier error O(1/n); L²-bounded approximators with error O(n^{−r})
-- statement:
--   Fix $0<p<1$ with $pn$ even. Let $\nu$ be uniform on $S(pn)$, and let $\mu_p^\circ=\mu_p(\,\cdot\mid H_{\rm even})$. Then
--   $$\max_\chi|\hat\nu(\chi)-\widehat{\mu_p^\circ}(\chi)|=O_p(n^{-1}).$$
--   For every fixed integer $r\ge1$ and every real $|f|\le1$ on the slice, there is a function $h:\mathbb F_2^n\to\mathbb R$ such that
--   $$\|h\|_{2,\mu_p}=O_{p,r}(1),\qquad\max_\chi|\langle f,\chi\rangle_\nu-\langle h,\chi\rangle_{\mu_p}|=O_{p,r}(n^{-r}).$$
--
--   Differences from the source:
--   - reading: O_p(n^{−1}), O_{p,r}(1), O_{p,r}(n^{−r}) → ∃ C, N (depending only on p, resp. p and r) such that for all n ≥ N with pn an even integer the bounds C/n, C, C/n^r hold for every f and every character; reason: the standard meaning of O-notation with the stated subscripts, uniform over f and χ
--   - encoding: real |f| ≤ 1 on the slice → f : F₂ⁿ → ℝ with |f x| ≤ 1 for x ∈ S(pn); reason: values off the slice do not enter ⟨f, χ⟩_ν
--   - encoding: for all sufficiently large n with pn even → ∃ N, ∀ n ≥ N, ∀ w : ℕ with (w : ℝ) = p·n and w even; reason: w is the integer pn; same instances
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §6.2, p. 44 (PDF 46), Lemma 6.10

import Mathlib
import Definitions.Def_SliceLinearity_Tests_BiasedAnalysis

set_option autoImplicit false

namespace SliceLinearity.Tests

/-- **Lemma 6.10** (Accurate approximators for the slice), p. 44 (PDF 46). Fix `0 < p < 1`. For `pn`
even, let `ν` be uniform on `S(pn)` and `μ°_p = μ_p( · | H_even)`. Then
`max_χ |ν̂(χ) − μ̂°_p(χ)| = O_p(n^{−1})`. For every fixed integer `r ≥ 1` and every real `|f| ≤ 1` on the
slice there is `h : F₂ⁿ → ℝ` with `‖h‖_{2,μ_p} = O_{p,r}(1)` and
`max_χ |⟨f, χ⟩_ν − ⟨h, χ⟩_{μ_p}| = O_{p,r}(n^{−r})`; the constants are uniform in `n`, `f` and `χ`. -/
theorem lemma_6_10 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ w : ℕ, (w : ℝ) = p * n → Even w → ∀ ξ : Cube n,
      |measFourier (unifOn (slice n w)) ξ - measFourier (muPEven p) ξ| ≤ C / (n : ℝ)) ∧
    ∀ r : ℕ, 1 ≤ r → ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ w : ℕ, (w : ℝ) = p * n → Even w →
      ∀ f : Cube n → ℝ, (∀ x ∈ slice n w, |f x| ≤ 1) →
        ∃ h : Cube n → ℝ, norm2W (muP p) h ≤ C ∧
          ∀ ξ : Cube n, |innerW (unifOn (slice n w)) f (chi ξ) - innerW (muP p) h (chi ξ)| ≤
            C / (n : ℝ) ^ r := by sorry

end SliceLinearity.Tests
