-- Prove2me | Theorems.Thm_PureDPQR_proposition_15
-- name    : PureDPQR.proposition_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:53.490387+00:00
-- url     : https://prove2.me/theorems/6d5df5c2-2702-4bf0-8e17-d3ee0a4ae03f
-- title:
--   Proposition 15, p.17 — the sparse Laplace mixture $H=(1-\pi)f+\pi\,l*f$ satisfies $H(x+t)\le e^{L|t|}H(x)$
-- statement:
--   **Proposition 15** (Logarithmic Lipschitz Bound via Sparse Laplace Mixture). Let $f:\mathbb R\to(0,1]$ be twice continuously differentiable with $(\log f)''(x)\ge-r^2$ for some $r>0$. Let $\pi\in(0,1)$, $\kappa\ge r$, and $l(t)=\frac\kappa2e^{-\kappa|t|}$. Define
--
--   $$H(x)=(1-\pi)f(x)+\pi\int_{-\infty}^{\infty}l(t)f(x+t)\,dt,\qquad u=\sqrt{2\log(4/\pi)},\qquad L=\kappa+ru .$$
--
--   Then $u>1$, $H$ is continuously differentiable, and for every $x,t\in\mathbb R$,
--
--   $$H(x+t)\le e^{L|t|}H(x).$$
--
--   This scalar statement is applied to one-dimensional slices in the proof of Lemma 14.
--
--   **Formalization Note** $(\log f)''$ is the second derivative of $x\mapsto\log f(x)$; the integral is a Lebesgue integral of a bounded integrable function.
--
--   Differences from the source:
--   - encoding: the parenthetical claim u := √(2 log(4/π)) > 1 in (4.9) → the conjunct 1 < u in the conclusion; reason: the paper asserts it as a fact (log(4/π) > log 4), not as a hypothesis
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Proposition 15, p.17 (PDF p.18); restated p.33 (PDF p.34)

import Mathlib

namespace PureDPQR

/-- **Proposition 15** (Logarithmic Lipschitz Bound via Sparse Laplace Mixture), p.17 (PDF p.18);
restated p.33 (PDF p.34).

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…).

"Let f : R → (0, 1] be twice continuously differentiable with (log f)′′(x) ≥ −r² for some r > 0.
For π ∈ (0, 1), κ ≥ r, and Laplace density l(t) := (κ/2)e^{−κ|t|}, define the mixture
H(x) := (1 − π)f(x) + π ∫_{−∞}^{∞} l(t)f(x + t) dt and parameters u := √(2 log(4/π)) > 1,
L := κ + ru = κ + r √(2 log(4/π)). (4.9) Then, H(x) is continuously differentiable, and for every
x ∈ R and t ∈ R, H(x + t) ≤ e^{L|t|} H(x). (4.10)"

**Formalization Note.** `π` is written `pert`. `(log f)''` is the second derivative
`deriv^[2] (fun x => log (f x))`, which is genuine since `f` is `C²` and positive. The integral is
the Bochner integral against Lebesgue measure; the integrand is bounded by the Laplace density
(`0 < f ≤ 1`), so it is integrable. The remark `u > 1` in (4.9) is a conclusion (it holds because
`log(4/π) > log 4`); it is not assumed. -/
theorem proposition_15 (f : ℝ → ℝ) (hf : ∀ x, 0 < f x ∧ f x ≤ 1) (hC2 : ContDiff ℝ 2 f)
    (r : ℝ) (hr : 0 < r) (hcurv : ∀ x, -(r ^ 2) ≤ deriv^[2] (fun z => Real.log (f z)) x)
    (pert κ : ℝ) (hpert : 0 < pert) (hpert1 : pert < 1) (hrκ : r ≤ κ) :
    let H : ℝ → ℝ := fun x =>
      (1 - pert) * f x + pert * ∫ t, κ / 2 * Real.exp (-κ * |t|) * f (x + t)
    let u : ℝ := Real.sqrt (2 * Real.log (4 / pert))
    let L : ℝ := κ + r * u
    1 < u ∧ ContDiff ℝ 1 H ∧ ∀ x t : ℝ, H (x + t) ≤ Real.exp (L * |t|) * H x := by sorry

end PureDPQR
