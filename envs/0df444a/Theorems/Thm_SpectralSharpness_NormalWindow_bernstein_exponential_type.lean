-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_bernstein_exponential_type
-- name    : SpectralSharpness.NormalWindow.bernstein_exponential_type
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:21:17.941782+00:00
-- url     : https://prove2.me/theorems/05e41b3f-b70e-408e-9701-597224205859
-- title:
--   Bernstein's inequality for entire functions of exponential type: $|g'(x)|\le\tau\sup_{\mathbb R}|g|$
-- statement:
--   This is the classical Bernstein inequality for entire functions of exponential type, cited in the proof of Lemma 9.1.
--
--   Let $\tau\ge0$ and $M\in\mathbb R$, and let $g:\mathbb C\to\mathbb C$ be an entire function of exponential type at most $\tau$: for every $\varepsilon>0$ there is $C$ with $|g(z)|\le Ce^{(\tau+\varepsilon)|z|}$ on $\mathbb C$. If $g$ is bounded by $M$ on the real axis, $|g(x)|\le M$ for all $x\in\mathbb R$, then
--
--   $$
--   |g'(x)|\le\tau M\qquad\text{for every }x\in\mathbb R .
--   $$
--
--   In the source it is applied to $g(w)=F(x_0+wv)$, the restriction of the entire extension of a band-limited trigonometric polynomial to a complex line, at $x=0$ with $\tau=d$ and $M=A$; this is where the dimension $n$ drops out of Lemma 9.1. The hypothesis is the classical growth condition of exponential type, not the stronger bound $|g(z)|\le Ce^{\tau|\operatorname{Im}z|}$.
--
--   Differences from the source:
--   - generalization: the bound at the single point 0, with τ = d and M = sup_ℝ |g| = A → the bound at every real x, for every τ ≥ 0 and every real bound M on |g| over ℝ; reason: the source's use is the instance x = 0, τ = d, M = A; the classical theorem (Boas 1954) is stated for every real x
--   - encoding: exponential type ≤ τ → ∀ ε > 0, ∃ C, ∀ z, ‖g z‖ ≤ C exp((τ + ε)‖z‖), plus Differentiable ℂ g; reason: the standard definition of an entire function of exponential type at most τ, equivalent to the limsup definition
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript (STOC 2027 submission #122; SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, §9, proof of Lemma 9.1, p. 27 (Bernstein's inequality for entire functions of exponential type [Boas 1954]); R. P. Boas, Entire Functions, Academic Press, 1954

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_ExponentialType

namespace SpectralSharpness.NormalWindow

/-- Bernstein's inequality for entire functions of exponential type [Boas 1954]: if `g` is
entire of exponential type at most `τ ≥ 0` and `|g(x)| ≤ M` for every real `x`, then
`|g'(x)| ≤ τ M` for every real `x`. -/
theorem bernstein_exponential_type (τ M : ℝ) (hτ : 0 ≤ τ) (g : ℂ → ℂ)
    (hg : IsEntireOfExponentialTypeLE τ g) (hM : ∀ x : ℝ, ‖g (x : ℂ)‖ ≤ M) :
    ∀ x : ℝ, ‖deriv g (x : ℂ)‖ ≤ τ * M := by sorry

end SpectralSharpness.NormalWindow
