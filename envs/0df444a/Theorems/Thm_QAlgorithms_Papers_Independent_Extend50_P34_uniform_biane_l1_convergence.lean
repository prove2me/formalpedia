-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_uniform_biane_l1_convergence
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.uniform_biane_l1_convergence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:20:35.664016+00:00
-- url     : https://prove2.me/theorems/13643e56-00b8-476f-a83c-9ffbdc6cf471
-- title:
--   Theorem 7.2
-- statement:
--   Fix $C>0$, a function $f:\mathbb N\to\mathbb N$ tending to infinity, and $0<\delta<1$. There is $d_0$, depending only on $C,f,\delta$, such that for every $d\ge d_0$ and every integer $n\ge1$ with $f(d)\le n\le Cd^2$, writing $\theta=\sqrt n/d$,
--
--   $$\Pr_{\lambda\sim\mathrm{SW}_d^n}[d_1(\bar\lambda,\Omega_\theta)\ge\delta]\le\delta.$$
--
--   Here $\bar\lambda(x)=\lambda(\sqrt n\,x)/\sqrt n$ is the scaled Russian boundary, $\Omega_\theta$ is the explicit Biane curve, and $d_1$ is the integral of absolute boundary difference. This is uniform in the moving parameter $n$, including sequences $\theta\to0$.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 60, Theorem 7.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 7.2, arXiv:1501.05028v1, PDF p.60. d0 is chosen before n. Scaled Russian boundary is distinct from EYD rows, and the Biane curve is given explicitly, including theta=0 and 1. -/
theorem uniform_biane_l1_convergence
    (C : ℝ) (hC : 0 < C) (f : ℕ → ℕ) (hf : Diverges f)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ∃ d0 : ℕ, 2 ≤ d0 ∧ ∀ d : ℕ, d0 ≤ d →
      ∀ n : ℕ, 0 < n → f d ≤ n → (n : ℝ) ≤ C*d^2 →
        event (n := n) (unif d) (fun lambda =>
          delta ≤ boundaryDistance (scaledBoundary lambda) (biane (Real.sqrt n/d))) ≤ delta := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
