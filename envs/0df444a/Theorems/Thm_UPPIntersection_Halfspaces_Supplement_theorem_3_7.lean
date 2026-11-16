-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_Supplement_theorem_3_7
-- name    : UPPIntersection.Halfspaces.Supplement.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:01:47.113207+00:00
-- url     : https://prove2.me/theorems/5534413e-d5ac-4289-a3e2-e772378ebbb8
-- title:
--   Theorem 3.7 — product Gegenbauer expansion of $H_{f,g}$ with $\sum_\ell|c_\ell|\le1$, uniformly convergent on $[-1,1]^k$
-- statement:
--   Let $d\ge2$ and let $f,g:(S^{d-1})^k\to\mathbb R^r$ be measurable with $\|f(x)\|_2,\|g(x)\|_2\le1$ for every $x$. Let $H=H_{f,g}:[-1,1]^k\to[-1,1]$ be their spherical symmetrization, $H(s)=\mathbb E_{(X,Y)\sim D_s}\langle f(X),g(Y)\rangle$. Then there are real coefficients $c_\ell$, indexed by $\ell=(\ell_1,\dots,\ell_k)\in\{0,1,2,\dots\}^k$, with
--   $$\sum_\ell|c_\ell|\le1\qquad\text{and}\qquad H(s_1,\dots,s_k)=\sum_\ell c_\ell\prod_{i=1}^kG^d_{\ell_i}(s_i)\quad\text{for every }s\in[-1,1]^k.$$
--   Moreover, the series converges uniformly on $[-1,1]^k$.
--
--   This is the series representation behind Theorem 3.1: since each product of Gegenbauer polynomials has controlled derivatives (Theorem 3.5) and the coefficients have total mass at most one, $H$ inherits derivative bounds.
--
--   **Formalization Note** The coefficient family is required to be absolutely summable, so the value of the sum does not depend on the order of summation (an unsummable family would have Lean sum $0$). Uniform convergence is stated for the paper's finite partial sums over the boxes $\|\ell\|_\infty\le m$; absolute summability with $|G^d_i|\le1$ makes every other exhaustion uniformly convergent as well.
--
--   Differences from the source:
--   - encoding: G^d_i defined as the unique degree-i polynomials orthogonal for v_d(t)=(1−t²)^((d−3)/2) on [−1,1] with G^d_i(1)=1 (Definition 3.3) → the published SphereSOS.Rate.geg, defined by G_0=1, G_1=t and (k+d−1)G_{k+2}=(2k+d)tG_{k+1}−(k+1)G_k; reason: this recurrence defines the same normalized Gegenbauer polynomials for every d ≥ 2 (Chebyshev polynomials at d=2); the identification is a fact to be used, not an assumption
--   - encoding: the series converges uniformly on [−1,1]^k → absolute summability, pointwise HasSum, and uniform convergence of the box partial sums ∑_{‖ℓ‖_∞≤m} on [−1,1]^k; reason: these are the paper's partial sums H_m (p. 19); with ∑|c_ℓ| ≤ 1 and |G^d_i| ≤ 1 all exhaustions converge uniformly to the same limit
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), pp. 18–19, Theorem 3.7 (proof on p. 19); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Sphere
import Definitions.Def_SphereSOS_Rate_Gegenbauer
import Definitions.Def_UPPIntersection_Halfspaces_Supplement_Defs

open MeasureTheory Filter

namespace UPPIntersection.Halfspaces.Supplement

/-- Bun–Juvekar, Theorem 3.7 (pp. 18–19). For measurable `f, g : (S^{d-1})^k → ℝ^r` with pointwise
Euclidean norms at most `1`, there are real coefficients `c_ℓ`, `ℓ ∈ ℕ^k`, with `∑_ℓ |c_ℓ| ≤ 1`
(absolutely summable), such that the spherical symmetrization satisfies
`H_{f,g}(s) = ∑_ℓ c_ℓ ∏_i G^d_{ℓ_i}(s_i)` for every `s ∈ [-1,1]^k`, and the series converges uniformly
on `[-1,1]^k` (its box partial sums over `‖ℓ‖_∞ ≤ m` converge uniformly to `H_{f,g}`). -/
theorem theorem_3_7 (d k r : ℕ) (hd : 2 ≤ d)
    (f g : (Fin k → Sph d) → EuclideanSpace ℝ (Fin r))
    (hf : Measurable f) (hg : Measurable g)
    (hf1 : ∀ x, ‖f x‖ ≤ 1) (hg1 : ∀ y, ‖g y‖ ≤ 1) :
    ∃ c : (Fin k → ℕ) → ℝ,
      Summable (fun ℓ => |c ℓ|) ∧ ∑' ℓ, |c ℓ| ≤ 1 ∧
      (∀ s ∈ Set.Icc (fun _ : Fin k => (-1 : ℝ)) (fun _ => 1),
        HasSum (fun ℓ => c ℓ * gegProd d ℓ s) (symH f g s)) ∧
      TendstoUniformlyOn (fun (m : ℕ) (s : Fin k → ℝ) => ∑ ℓ ∈ boxIdx k m, c ℓ * gegProd d ℓ s)
        (symH f g) atTop (Set.Icc (fun _ => -1) (fun _ => 1)) := by sorry

end UPPIntersection.Halfspaces.Supplement
