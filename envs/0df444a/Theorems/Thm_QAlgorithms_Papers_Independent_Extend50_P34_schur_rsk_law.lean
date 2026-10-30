-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_schur_rsk_law
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.schur_rsk_law
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:49:04.902325+00:00
-- url     : https://prove2.me/theorems/11fc9bbd-b4cf-498d-9b68-a34066bb2b2b
-- title:
--   Remark 2.24
-- statement:
--   Let $\rho$ be a $d$-dimensional density matrix, $d\ge1$, and let $D$ list its eigenvalues in any order. For every $n\ge0$ and every partition $\lambda\vdash n$ of height at most $d$,
--
--   $$\mathrm{SW}_\rho^n(\lambda)=\Pr_{w\sim D^{\otimes n}}[\operatorname{RSK}(w)=\lambda].$$
--
--   The left side is the Born mass of the full shape-isotypic projector. This supplies a classical random-word realization of the physical Schur law.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 21, Remark 2.24

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Remark 2.24, arXiv:1501.05028v1, PDF p.21.  -/
theorem schur_rsk_law
    (d n : ℕ) (hd : 0 < d) (rho : Matrix (Fin d) (Fin d) ℂ)
    (hrho : IsDensityMatrix rho) (eta : Fin d → ℝ)
    (heta : Learning.IsDistribution eta)
    (hspec : ∃ pi : Equiv.Perm (Fin d), eta = decreasingSpectrum rho ∘ pi)
    (lambda : Schur.Partition d n) :
    sw rho lambda = ∑ w : Fin n → Fin d,
      if rsk w = lambda.val then wordMass eta w else 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
