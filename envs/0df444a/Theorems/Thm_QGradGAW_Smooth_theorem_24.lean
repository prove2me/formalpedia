-- Prove2me | Theorems.Thm_QGradGAW_Smooth_theorem_24
-- name    : QGradGAW.Smooth.theorem_24
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:26.589529+00:00
-- url     : https://prove2.me/theorems/1820a365-9cbc-44b6-8699-832b029e0aed
-- title:
--   Theorem 24, p. 29 — |∇f(0)y − f_(2m)(y)| ≤ Σ_{k≥2m+1} (8Rcm√d)ᵏ for all but a 1/1000 fraction of y ∈ R·G_nᵈ
-- statement:
--   Let $R>0$, $m\ge1$, $n\ge0$ and $c\in\mathbb R$, and let $f:\mathbb R^d\to\mathbb R$ be smooth and analytic in the sense of Definition 5, with
--   $$|\partial_\alpha f(0)|\le c^k\,k^{k/2}\qquad\text{for all }k\ge1,\ \alpha\in[d]^k .$$
--   Assume $8Rcm\sqrt d<1$. Then
--   $$\big|\nabla f(0)\cdot y-f_{(2m)}(y)\big|\;\le\;\sum_{k=2m+1}^{\infty}\big(8Rcm\sqrt d\big)^k$$
--   for all but a $1/1000$ fraction of the points $y\in R\cdot G_n^d$; that is, the number of grid labels for which the inequality fails is at most $(2^n)^d/1000$.
--
--   This is the approximation guarantee that lets Jordan's algorithm (Theorem 21) be run on the central difference $f_{(2m)}$ instead of $f$: on most of a hypercube of edge length $R$ around $0$, $f_{(2m)}$ is very close to the linear function $y\mapsto\nabla f(0)\cdot y$.
--
--   **Formalization Note** $\mathbb N$ starts at $1$ in the paper, so the derivative bound is assumed for $k\ge1$ and $m\ge1$ (for $m=0$ the claim is false). The hypothesis $8Rcm\sqrt d<1$ is the condition under which the printed series is a finite number; without it the right-hand side is $+\infty$ and the paper's claim is empty, while the Lean `tsum` of a divergent series would be $0$. "Analytic" is the Taylor representation (5) at $0$ together with $C^\infty$ smoothness (which Definition 5 presupposes). $\nabla f(0)\cdot y$ is the derivative of $f$ at $0$ applied to $y$.
-- source:
--   Gilyén, Arunachalam, Wiebe, Optimizing quantum optimization algorithms via faster quantum gradient computation, arXiv:1711.00465v3, p. 29, Theorem 24 (restated with proof p. 54)

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

namespace QGradGAW.Smooth

open QAlgorithms

/-- arXiv:1711.00465v3, p. 29 (restated with proof p. 54), Theorem 24: let `R > 0`, `m ∈ ℕ₊` and
let `f : ℝ^d → ℝ` be analytic (Definition 5) with `|∂_α f(0)| ≤ c^k k^{k/2}` for all `k ∈ ℕ₊`
and `α ∈ [d]^k`. Then `|∇f(0) y − f_(2m)(y)| ≤ Σ_{k=2m+1}^∞ (8Rcm√d)^k` for all but a `1/1000`
fraction of the points `y ∈ R · G_n^d`, i.e. the number of grid labels `x ∈ (Qubits n)^d` at
which the bound fails for `y = R · x̂` is at most `(2^n)^d / 1000`. The hypothesis
`8Rcm√d < 1` is the condition under which the printed series is a finite number. -/
theorem theorem_24 (d n m : ℕ) (hm : 1 ≤ m) (R c : ℝ) (hR : 0 < R)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (han : IsTaylorRep f 0)
    (hder : ∀ k : ℕ, 1 ≤ k → ∀ α : Fin k → Fin d,
      |partialAlpha f k α 0| ≤ c ^ k * Real.sqrt k ^ k)
    (hq : 8 * R * c * m * Real.sqrt d < 1) :
    ((Finset.univ.filter fun x : Fin d → Qubits n =>
        ¬ |fderiv ℝ f 0 (R • gridVec x) - centralDiff m f (R • gridVec x)| ≤
          ∑' k : ℕ, (8 * R * c * m * Real.sqrt d) ^ (2 * m + 1 + k)).card : ℝ) ≤
      (2 ^ n : ℝ) ^ d / 1000 := by sorry

end QGradGAW.Smooth
