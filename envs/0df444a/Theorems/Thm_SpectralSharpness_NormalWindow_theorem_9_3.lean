-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_theorem_9_3
-- name    : SpectralSharpness.NormalWindow.theorem_9_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:21:28.065182+00:00
-- url     : https://prove2.me/theorems/a45aed9e-28d2-487d-9919-15f628c3d7d6
-- title:
--   Theorem 9.3 — window along the normal: $|\{t\in[t_-,t_+]:|f(p+tn_p)|<\gamma\}|\ge 2\gamma/(dA)$
-- statement:
--   Let $f$ be a real trigonometric polynomial on $\mathbb T^n$ (represented on $\mathbb R^n$) whose spectrum lies in the Euclidean ball $B_d=\{k\in\mathbb Z^n:\|k\|_2\le d\}$, $d\ge0$, and let $A$ bound its sup norm, $|f(x)|\le A$ for all $x$. Let $\gamma\in(0,1)$.
--
--   Let $p\in\mathbb R^n$ be a point and $v\in\mathbb R^n$ a unit vector (in the source, $p$ is a point of the boundary $\Sigma$ of a $C^2$ domain and $v=n_p$ its outward unit normal), and suppose the classifier crosses from $-\gamma$ to $\gamma$ along the line $p+tv$: there are $t_-<0<t_+$ with
--   $$
--   f(p+t_-v)\le-\gamma,\qquad f(p+t_+v)\ge\gamma .
--   $$
--   Then the set of parameters in $[t_-,t_+]$ at which $f$ is uncertain has one-dimensional Lebesgue measure at least $2\gamma/(dA)$:
--   $$
--   \Big|\{t\in[t_-,t_+]:\ |f(p+t v)|<\gamma\}\Big|\ \ge\ \frac{2\gamma}{d\,A}.
--   $$
--
--   This is the $n$-dimensional form of the paper's sharpness–bandwidth exchange rate: a band-limited classifier with Euclidean-ball spectrum cannot make the transition from $-\gamma$ to $\gamma$ in less than $2\gamma/(dA)$ along any line, with the same constant as in dimension one and no factor of $n$. Integrated over the resolved part of the boundary it bounds the volume of the uncertainty region from below.
--
--   **Formalization Note** The measure is `volume` on $\mathbb R$ (an extended nonnegative real), compared with `ENNReal.ofReal (2γ/(dA))`. If $dA=0$, Lean's division returns $0$; under the hypotheses this case cannot occur ($d=0$ or $A=0$ forces $f$ to be constant, which cannot cross from $-\gamma$ to $\gamma$), so no source instance is lost.
--
--   Differences from the source:
--   - generalization: p ∈ Σ* (a point of the C² boundary Σ of a domain Ω ⊂ 𝕋ⁿ whose outward unit normal n_p is γ-resolved at scale η, Definition 9.2) with t± the witnesses of Definition 9.2 → any point p ∈ ℝⁿ, any unit vector v and any t₋ < 0 < t₊ with f(p + t₋v) ≤ −γ and f(p + t₊v) ≥ γ; reason: every source instance (p, n_p, t±) is such an instance; Ω, Σ, the C² condition and the bound |t±| ≤ η are not used by the statement
--   - generalization: A = ∥f∥∞ → any A with |f(x)| ≤ A for all x; reason: A = ∥f∥∞ satisfies the hypothesis, so the source statement is the special case
--   - generalization: d is the degree (bandwidth) → any real d ≥ 0; reason: B_d = {k : ∥k∥₂ ≤ d} is defined for real d, and every source instance has d ≥ 0
--   - encoding: f band-limited on 𝕋ⁿ and the points p + t n_p of 𝕋ⁿ → a 2π-periodic real function on ℝⁿ given by a finite sum of c_k e^{i k·x}, k ∈ ℤⁿ ∩ B_d, evaluated at p + t v ∈ ℝⁿ; reason: same values; the parameter set is a subset of the real interval [t₋, t₊] in both
--   - encoding: Lebesgue measure |·| ≥ 2γ/(dA) → volume (in ℝ≥0∞) ≥ ENNReal.ofReal (2γ/(dA)); reason: dA > 0 in every instance satisfying the hypotheses, so the real fraction is the source's value
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript (STOC 2027 submission #122; SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 9.3, p. 27, with the §9 Setup and Definition 9.2, p. 27

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_BandLimited

open MeasureTheory

namespace SpectralSharpness.NormalWindow

/-- Theorem 9.3 (window along the normal). Let `f` be a real trigonometric polynomial on `𝕋ⁿ`
with spectrum in the Euclidean ball `‖k‖₂ ≤ d` (`d ≥ 0`), with `|f| ≤ A` everywhere, and let
`γ ∈ (0, 1)`. Let `p` be a point and `v` a unit vector, and suppose `t₋ < 0 < t₊` with
`f(p + t₋ v) ≤ -γ` and `f(p + t₊ v) ≥ γ`. Then the Lebesgue measure of
`{t ∈ [t₋, t₊] : |f(p + t v)| < γ}` is at least `2γ / (d A)`. -/
theorem theorem_9_3 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (d A γ : ℝ) (hd : 0 ≤ d)
    (hf : IsBandLimitedBall d f) (hA : ∀ x, |f x| ≤ A) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (p v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) (tm tp : ℝ) (htm : tm < 0) (htp : 0 < tp)
    (hfm : f (p + tm • v) ≤ -γ) (hfp : γ ≤ f (p + tp • v)) :
    ENNReal.ofReal (2 * γ / (d * A)) ≤
      volume {t : ℝ | t ∈ Set.Icc tm tp ∧ |f (p + t • v)| < γ} := by sorry

end SpectralSharpness.NormalWindow
