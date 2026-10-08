-- Prove2me | Theorems.Thm_PrimalDualLDR_RandomRecourse_claim_3_13
-- name    : PrimalDualLDR.RandomRecourse.claim_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:42:56.005624+00:00
-- url     : https://prove2.me/theorems/892c8c03-7677-402f-969e-7db95c1e2f92
-- title:
--   §3.2, p. 12 — the μth equality constraint of 𝒮𝒫^u holds P-a.s. iff H_μ = 0 (Ξ with relative interior)
-- statement:
--   Assume the standing assumptions of §3: $\Xi=\{\xi:\ e_1^\top\xi=1,\ \xi^\top W_\ell\xi\ge0,\ \ell=1,\dots,l\}$ is the support of the probability measure $\mathbb P$, it is nonempty and bounded, it spans $\mathbb R^k$, and every $W_\ell$ is symmetric. Assume in addition that $\Xi$ has a relative interior point: some $\xi_0\in\Xi$ and $r>0$ satisfy $\xi\in\Xi$ whenever $e_1^\top\xi=1$ and $\|\xi-\xi_0\|<r$.
--
--   Let $X\in\mathbb R^{n\times k}$, let $S_\mu$ be a symmetric $k\times k$ matrix and $\mu\in\{1,\dots,m\}$, and set
--   $$
--   H_\mu=\tfrac12\big(A_\mu X+X^\top A_\mu^\top-e_1b_\mu^\top-b_\mu e_1^\top\big)+S_\mu .
--   $$
--   Then
--   $$
--   \xi^\top A_\mu X\xi+\xi^\top S_\mu\xi=b_\mu^\top\xi\quad\mathbb P\text{-a.s.}\qquad\Longleftrightarrow\qquad H_\mu=0 .
--   $$
--
--   This turns each semi-infinite equality constraint of $\mathcal{SP}^u$ into a finite linear matrix equation, which is the equality constraint of the SDP (3.14).
--
--   **Formalization Note** The relative-interior hypothesis is a repair. The paper deduces "the interior of $\mathrm{cone}(\Xi)$ is nonempty" from "$\Xi$ spans $\mathbb R^k$", which needs $\Xi$ to have dimension $k-1$; for a nonconvex $\Xi$ of type (3.11) with $l\ge2$ this fails (e.g. $k=2$ and $\Xi=\{(1,a),(1,b)\}$ cut out by $(u-a)(u-b)\ge0$ and $-(u-a)(u-b)\ge0$, where $H=\begin{pmatrix}ab&-(a+b)/2\\-(a+b)/2&1\end{pmatrix}\ne0$ vanishes on $\Xi$). The paper states on p. 10 that spanning is equivalent to "dimension $k-1$", and the added hypothesis is that reading. For $l=1$ it follows from the standing assumptions. $S_\mu$ is assumed symmetric, as in $\mathcal{SP}^u$; without symmetry only the symmetric part of $H_\mu$ would be determined.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 12, §3.2, (3.13) and the paragraph after it

import Mathlib
import Definitions.Def_PrimalDualLDR_RandomRecourse_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.RandomRecourse

/-- **Kuhn, Wiesemann, Georghiou (preprint 2009), §3.2, p. 12 (unnumbered, around (3.13)).**
Under the standing assumptions of §3, for a decision `X ∈ ℝ^{n×k}`, a symmetric slack matrix
`S_μ ∈ 𝕊` and a row `μ`, the `μ`th equality constraint of `𝒮𝒫^u`,
`ξᵀA_μXξ + ξᵀS_μξ = b_μᵀξ` `P`-almost surely, holds if and only if
`H_μ = ½(A_μX + XᵀA_μᵀ − e_1b_μᵀ − b_μe_1ᵀ) + S_μ = 0`.

Repair: the hypothesis `hrelint` (some point of `Ξ` has a neighbourhood, relative to the
hyperplane `{e_1ᵀξ = 1}`, contained in `Ξ`) is added. The paper derives "the interior of
`cone(Ξ)` is nonempty" from "`Ξ` spans `ℝ^k`", which fails when `Ξ` is not convex (for `l ≥ 2`,
`Ξ` can be two points); `hrelint` is the paper's "`Ξ` has dimension `k − 1`" (p. 10). For
`l = 1` it follows from the standing assumptions. -/
theorem claim_3_13 (σ : Setting) (hσ : σ.Standing)
    (hrelint : ∃ ξ₀ ∈ σ.Xi, ∃ r : ℝ, 0 < r ∧
      ∀ ξ : Fin σ.k → ℝ, σ.e1 ⬝ᵥ ξ = 1 → dist ξ ξ₀ < r → ξ ∈ σ.Xi)
    (X : Matrix (Fin σ.n) (Fin σ.k) ℝ) (Sμ : Matrix (Fin σ.k) (Fin σ.k) ℝ) (hS : Sμ.IsSymm)
    (μ : Fin σ.m) :
    (∀ᵐ ξ ∂σ.P, ξ ⬝ᵥ ((σ.A μ * X) *ᵥ ξ) + ξ ⬝ᵥ (Sμ *ᵥ ξ) = σ.B μ ⬝ᵥ ξ) ↔
      σ.H X Sμ μ = 0 := by sorry

end PrimalDualLDR.RandomRecourse
