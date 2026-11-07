-- Prove2me | Theorems.Thm_QuasiPolyTrace_lemma_13
-- name    : QuasiPolyTrace.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:31:55.142001+00:00
-- url     : https://prove2.me/theorems/b380ed23-09fb-4c4d-8a08-2030256f8261
-- title:
--   Lemma 13 — summed 2nd and 3rd order statistics fix a sequence up to shift
-- statement:
--   Let $\tau>0$, $N\in\mathbb N$, and let $f,g$ be length-$N$ real sequences (indices mod $N$) with $|f(j)|,|g(j)|\le1$; let $F,G$ be their discrete Fourier transforms. Let $\gamma\in[22,N)$ and assume that $|F(\xi)-G(\xi)|\ge\tau$ for at least a $\tfrac{9}{10}$ fraction of the integers $\xi$ with $|\xi|\le\gamma$. Assume all summed second and third order statistics are close:
--
--   $$
--   \Big|\sum_j f(j)f(j+\ell)-\sum_j g(j)g(j+\ell)\Big|\le\frac{\tau^4}{2000N^4},\qquad
--   \Big|\sum_j f(j)f(j+\ell_1)f(j+\ell_2)-\sum_j g(j)g(j+\ell_1)g(j+\ell_2)\Big|\le\frac{\tau^4}{2000N^4}
--   $$
--
--   for all shifts $\ell,\ell_1,\ell_2$. Then there is $\alpha\in\mathbb R$ with
--
--   $$
--   \big|F(\xi)-G(\xi)e^{i\xi\alpha}\big|\le\tau\qquad\text{for every integer }\xi\text{ with }|\xi|\le\tfrac12\gamma .
--   $$
--
--   So $f$ is close to a shift of $g$ at low frequencies unless a summed statistic of order $2$ or $3$ separates them.
--
--   Differences from the source:
--   - encoding: indices {1, …, N} mod N → Fin N with addition mod N; reason: the same residues; the DFT kernel takes the same value at N and 0
--   - reading: integer frequencies up to frequency γ; summed 2nd and 3rd order statistics δ-close → integers ξ with −⌊γ⌋ ≤ ξ ≤ ⌊γ⌋; |s_f(ℓ) − s_g(ℓ)| ≤ δ and |s_f(ℓ₁, ℓ₂) − s_g(ℓ₁, ℓ₂)| ≤ δ for all shifts; reason: the statistics are those of Lemmas 11–12 (p.14); "close" is the absolute difference
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 13, p.15 (with the summed statistics of Lemmas 11–12, p.14)

import Mathlib
import Definitions.Def_QuasiPolyTrace_dft

namespace QuasiPolyTrace

/-- **Lemma 13 (summed 2nd and 3rd order statistics determine a sequence up to shift).** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…),
Lemma 13, p.15: "For any τ > 0 and N ∈ N, the following holds. Let f, g be length N sequences of real
numbers of size at most 1. Letting F, G be the discrete Fourier transforms of f, g respectively, assume
|F − G| is at least τ large on ≥ 9/10 fraction of (integer) frequencies up to frequency γ, for
γ ∈ [22, N). If all summed 2nd and 3rd order statistics of f, g are all ≤ τ⁴/(2000N⁴) close to each other
then 'f is close to a shift of g at low frequencies' in the sense that there exists a real number α such
that for all (integer) frequencies |ξ| up to ½γ, we have F(ξ) is within τ of G(ξ)e^{iξα}."

**Formalization Note.**
* Sequences are `Fin N → ℝ` with indices mod `N` (`Fin` addition is mod `N`); `dft` is the discrete
  Fourier transform with kernel `e^{2πi jξ/N}` (proof of Lemma 12, p.14).
* The summed statistics are those of Lemmas 11–12 (p.14): `s(ℓ) = ∑_j f(j) f(j+ℓ)` and
  `s(ℓ₁, ℓ₂) = ∑_j f(j) f(j+ℓ₁) f(j+ℓ₂)`, indices mod `N`; "δ close" is `|s_f − s_g| ≤ δ` for every
  `ℓ` and every `(ℓ₁, ℓ₂)`.
* The integer frequencies "up to frequency γ" are the integers `ξ` with `|ξ| ≤ γ`, i.e.
  `−⌊γ⌋ ≤ ξ ≤ ⌊γ⌋`; the 9/10 fraction is a ratio of counts. -/
theorem lemma_13 (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (f g : Fin N → ℝ) (hf : ∀ j, |f j| ≤ 1)
    (hg : ∀ j, |g j| ≤ 1) (γ : ℝ) (hγ₁ : 22 ≤ γ) (hγ₂ : γ < N)
    (hfreq : (9 / 10 : ℝ) * ((Finset.Icc (-⌊γ⌋) ⌊γ⌋).card : ℝ) ≤
      (((Finset.Icc (-⌊γ⌋) ⌊γ⌋).filter (fun ξ => τ ≤ ‖dft N f ξ - dft N g ξ‖)).card : ℝ))
    (h₂ : ∀ ℓ : Fin N, |∑ j, f j * f (j + ℓ) - ∑ j, g j * g (j + ℓ)| ≤ τ ^ 4 / (2000 * (N : ℝ) ^ 4))
    (h₃ : ∀ ℓ₁ ℓ₂ : Fin N, |∑ j, f j * f (j + ℓ₁) * f (j + ℓ₂) - ∑ j, g j * g (j + ℓ₁) * g (j + ℓ₂)|
      ≤ τ ^ 4 / (2000 * (N : ℝ) ^ 4)) :
    ∃ α : ℝ, ∀ ξ : ℤ, |(ξ : ℝ)| ≤ γ / 2 →
      ‖dft N f ξ - dft N g ξ * Complex.exp (Complex.I * (ξ : ℂ) * (α : ℂ))‖ ≤ τ := by sorry

end QuasiPolyTrace
