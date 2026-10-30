-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_shifted_schur_weighted_cancellation
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.shifted_schur_weighted_cancellation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:02:15.852835+00:00
-- url     : https://prove2.me/theorems/a775bf40-73a1-468d-9dc1-a4851bc57936
-- title:
--   Theorem 4.7
-- statement:
--   Let $d\ge1$, $n\ge0$, $\sum_i x_i=0$, and $\mu\vdash r_1$ with $0<\ell(\mu)\le d$. For $r_2\ge r_1$,
--
--   $$\sum_{\substack{\nu\vdash r_2\ell(\nu)\le d}}\frac{s_\nu(x)}{d^{\uparrow\nu}}\mathbb E_{\lambda\sim\mathrm{SW}_d^n}[s_\mu^*(\lambda)s_\nu^*(\lambda)]=\mathbf1_{r_2=r_1}\frac{s_\mu(x)}{d^{|\mu|}}n^{\downarrow|\mu|}.$$
--
--   This is a weighted cancellation identity; it does not assert pairwise orthogonality of shifted Schur observables.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 36, Theorem 4.7

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 4.7, arXiv:1501.05028v1, PDF p.36. No pairwise orthogonality premise or conclusion is inserted; weights and the size indicator are essential. -/
theorem shifted_schur_weighted_cancellation
    (d n r2 : ℕ) (hd : 0 < d) (x : Fin d → ℝ) (hx : ∑ i, x i = 0)
    (mu : YoungDiagram) (hmu : 0 < mu.colLen 0) (hheight : mu.colLen 0 ≤ d)
    (hr : mu.card ≤ r2) :
    (∑ nu ∈ diagrams d r2, schurAt nu x / contentProduct d nu *
      expect (n := n) (unif d) (fun lambda => shiftedSchur mu lambda * shiftedSchur nu lambda)) =
      (if r2 = mu.card then 1 else 0) * schurAt mu x / (d : ℝ)^mu.card * falling n mu.card := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
