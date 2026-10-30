-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_scaled_boundary_bounded_support
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.scaled_boundary_bounded_support
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:21:20.056197+00:00
-- url     : https://prove2.me/theorems/b6334d9d-82d0-48ee-98a1-940210fedfdb
-- title:
--   Proposition 7.3
-- statement:
--   In the regime $f(d)\le n\le Cd^2$, with fixed $C>0$, $f(d)\to\infty$, and $0<\delta<1$, there are $B>0$ and $d_0$, depending only on these fixed data, such that uniformly for $d\ge d_0$ and every allowed $n$,
--
--   $$\Pr_{\lambda\sim\mathrm{SW}_d^n}[\bar\lambda(x)=|x|\text{ for all }|x|>B]\ge1-\delta/2.$$
--
--   Thus the random scaled boundary differs from $|x|$ only on an interval of bounded width with the stated probability. This supplies uniform support control for the L1 limit argument.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 61, Proposition 7.3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Proposition 7.3, arXiv:1501.05028v1, PDF p.61. Extraction reads 1-2delta; the PDF prints 1-delta/2. The proof allows dependence on C and delta, and yields a fixed symmetric containing interval. -/
theorem scaled_boundary_bounded_support
    (C : ℝ) (hC : 0 < C) (f : ℕ → ℕ) (hf : Diverges f)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ∃ B : ℝ, 0 < B ∧ ∃ d0 : ℕ, 2 ≤ d0 ∧ ∀ d : ℕ, d0 ≤ d →
      ∀ n : ℕ, 0 < n → f d ≤ n → (n : ℝ) ≤ C*d^2 →
        event (n := n) (unif d) (fun lambda =>
          ∀ x : ℝ, B < |x| → scaledBoundary lambda x = |x|) ≥ 1-delta/2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
