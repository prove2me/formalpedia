-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_schur_ratio_squared_identity
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.schur_ratio_squared_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:00:29.052637+00:00
-- url     : https://prove2.me/theorems/45c57d66-397d-4a55-8f3c-687174c74e59
-- title:
--   Theorem 4.4
-- statement:
--   Let $d\ge1$, $n\ge0$, and $x\in\mathbb R^d$ satisfy $\sum_i x_i=0$. Then
--
--   $$\mathbb E_{\lambda\sim\mathrm{SW}_d^n}\left(\frac{s_\lambda(1+x)}{s_\lambda(1^d)}-1\right)^2=\sum_{\substack{1\le|\mu|\le n\ell(\mu)\le d}}\frac{s_\mu(x)^2}{d^{\uparrow\mu}d^{|\mu|}}n^{\downarrow|\mu|}.$$
--
--   The denominator is positive on the relevant shapes. No nonnegativity restriction on $1+x_i$ is needed: this is a real polynomial identity underlying the chi-squared formula.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 35, Theorem 4.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 4.4, arXiv:1501.05028v1, PDF p.35. Finite sum k≤n is exact since falling factorials vanish above n; no extraneous x_i≥-1 premise. -/
theorem schur_ratio_squared_identity
    (d n : ℕ) (hd : 0 < d) (x : Fin d → ℝ) (hx : ∑ i, x i = 0) :
    expect (n := n) (unif d) (fun lambda =>
      (schurAt lambda (fun i => 1+x i) / schurAt lambda (fun _ : Fin d => 1) - 1)^2) =
      ∑ k ∈ Finset.Icc 1 n, ∑ mu ∈ diagrams d k,
        schurAt mu x ^ 2 / (contentProduct d mu * (d : ℝ)^k) * falling n k := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
