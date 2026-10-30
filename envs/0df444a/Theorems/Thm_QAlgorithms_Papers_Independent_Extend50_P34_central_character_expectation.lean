-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_central_character_expectation
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.central_character_expectation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:52:01.795284+00:00
-- url     : https://prove2.me/theorems/44707553-5f5a-4101-be95-465ab58da045
-- title:
--   Proposition 2.34
-- statement:
--   Let $\rho$ be a $d$-dimensional density matrix with eigenvalues $\eta_1,\ldots,\eta_d$, and let $\mu\vdash k$. For every $n\ge0$,
--
--   $$\mathbb E_{\lambda\sim\mathrm{SW}_\rho^n}p_\mu^\sharp(\lambda)=n^{\downarrow k}p_\mu(\eta).$$
--
--   Here $p_\mu$ is the product of ordinary power sums, and $p_\mu^\sharp$ is the normalized Specht central character. If $n<k$, both sides vanish. This gives exact moments of the physical Schur distribution.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 26, Proposition 2.34

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Proposition 2.34, arXiv:1501.05028v1, PDF p.26.  -/
theorem central_character_expectation
    (d n : ℕ) (hd : 0 < d) (rho : Matrix (Fin d) (Fin d) ℂ)
    (hrho : IsDensityMatrix rho) (mu : YoungDiagram) :
    (∑ lambda : Schur.Partition d n, sw rho lambda * sharp mu lambda.val) =
      falling n mu.card * powerParts (mu.rowLens : Multiset ℕ) (decreasingSpectrum rho) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
