-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_paninski_exact_even_expansion
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.paninski_exact_even_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:06:22.45225+00:00
-- url     : https://prove2.me/theorems/6a9d92f5-69d3-4e57-976b-9b28e4450bd8
-- title:
--   Theorem 4.19
-- statement:
--   For even $d\ge2$, $n\ge0$, and $0\le\epsilon\le1/2$,
--
--   $$d_{\chi^2}(\mathrm{SW}_{P_d^\epsilon}^n,\mathrm{SW}_d^n)=\sum_{\substack{2\le k\le n\k\text{ even}}}n^{\downarrow k}(2\epsilon)^{2k}d^{-k}\frac1{(k!!)^2}\sum_{\substack{\mu\vdash k\text{ balanced}\0<\ell(\mu)\le d}}\chi_\mu(2^{k/2})^2\frac{d^{\uparrow[\mu]_{\rm even}}}{d^{\uparrow[\mu]_{\rm odd}}}.$$
--
--   The sums are finite and every content-product denominator is positive under the height restriction. This exact expansion leads to the exponential chi-squared bound.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 42, Theorem 4.19

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 4.19, arXiv:1501.05028v1, PDF p.42. Both the exponent 2k on 2epsilon and the square on k!! are retained. k≤n replaces only vanishing terms. -/
theorem paninski_exact_even_expansion
    (d n : ℕ) (hd : 0 < d) (heven : Even d)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (he1 : epsilon ≤ 1/2) :
    chiSq (swSpectrum (n := n) (paninski d epsilon)) (swSpectrum (n := n) (unif d)) =
      ∑ k ∈ (Finset.Icc 2 n).filter Even,
        falling n k * (2*epsilon)^(2*k) / (d : ℝ)^k *
          (1 / evenDoubleFactorial k ^ 2 *
            ∑ mu ∈ (diagrams d k).filter DominoBalanced,
              classCharacter mu (Multiset.replicate (k/2) 2)^2 *
                parityProduct d mu true / parityProduct d mu false) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
