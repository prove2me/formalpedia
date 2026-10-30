-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_absolute_centered_boundary_moment
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.absolute_centered_boundary_moment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:22:03.981439+00:00
-- url     : https://prove2.me/theorems/0516794d-cc5b-4edd-9a30-9763bd0d5976
-- title:
--   Lemma 7.6
-- statement:
--   Fix $C>0$, $f(d)\to\infty$, and an integer $k\ge1$. With $\widetilde q_k$ defined by the explicit boundary-moment subtraction on p.62,
--
--   $$\mathbb E_{\lambda\sim\mathrm{SW}_d^n}\left|\frac{\widetilde q_k(\lambda)}{\sqrt n}\right|=o_d(1)$$
--
--   uniformly over all integers $n\ge1$ satisfying $f(d)\le n\le Cd^2$. The absolute value is essential. This controls the moments needed for the L1 convergence argument.
--
--   Write $\lambda(x)$ for the unscaled Russian boundary and $\widetilde p_j(\lambda)=j(j-1)\int_{\mathbb R}x^{j-2}(\lambda(x)-|x|)/2\,dx$. The centered quantity is
--
--   $$\widetilde q_k(\lambda)=\frac{\widetilde p_{k+1}(\lambda)}{(k+1)n^{k/2}}-\sum_{\ell=1}^{\lfloor(k+1)/2\rfloor}\frac{k^{\downarrow(2\ell-1)}}{(k+1-\ell)\ell!(\ell-1)!}\frac{n^{k/2+1-\ell}}{d^{k+1-2\ell}}.$$
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 62, Lemma 7.6

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Lemma 7.6, arXiv:1501.05028v1, PDF p.62. The PDF visibly has absolute-value bars. qTilde is computed from the boundary integral and deterministic Biane moments; it is not a supplied centered variable. -/
theorem absolute_centered_boundary_moment
    (C : ℝ) (hC : 0 < C) (f : ℕ → ℕ) (hf : Diverges f)
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ d0 : ℕ, 2 ≤ d0 ∧
      ∀ d : ℕ, d0 ≤ d → ∀ n : ℕ, 0 < n → f d ≤ n → (n : ℝ) ≤ C*d^2 →
        expect (n := n) (unif d) (fun lambda => |qTilde k n d lambda / Real.sqrt n|) ≤ epsilon := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
