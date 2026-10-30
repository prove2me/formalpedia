-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_low_weight_observable_expectation
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.low_weight_observable_expectation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:22:46.406842+00:00
-- url     : https://prove2.me/theorems/70f5fb78-154d-4b5e-aeeb-3ec3f96d9d3f
-- title:
--   Proposition 7.7
-- statement:
--   Fix $C>0$, $f(d)\to\infty$, an integer $k\ge0$, and a real observable $O=\sum_\mu a_\mu p_\mu^\sharp$ of weight at most $2k$, with finitely many coefficients fixed independently of $d,n$. Then
--
--   $$\mathbb E_{\lambda\sim\mathrm{SW}_d^n}\left[\frac{O(\lambda)}{n^{k+1}}\right]=o_d(1)$$
--
--   uniformly for $1\le n$, $f(d)\le n\le Cd^2$. This is convergence of a signed expectation, rather than an expectation of absolute value. It includes constant observables and controls lower-weight correction terms.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 63, Proposition 7.7

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Proposition 7.7, arXiv:1501.05028v1, PDF p.63. Absolute value is outside the signed expectation, the epsilon-definition of o(1). Real coefficients and the observable are fixed before d,n; k=0 includes constants. -/
theorem low_weight_observable_expectation
    (C : ℝ) (hC : 0 < C) (f : ℕ → ℕ) (hf : Diverges f)
    (k : ℕ) (a : YoungDiagram →₀ ℝ) (ha : ∀ mu ∈ a.support, observableWeight mu ≤ 2*k) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ d0 : ℕ, 2 ≤ d0 ∧
      ∀ d : ℕ, d0 ≤ d → ∀ n : ℕ, 0 < n → f d ≤ n → (n : ℝ) ≤ C*d^2 →
        |expect (n := n) (unif d) (realObservable a) / (n : ℝ)^(k+1)| ≤ epsilon := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
