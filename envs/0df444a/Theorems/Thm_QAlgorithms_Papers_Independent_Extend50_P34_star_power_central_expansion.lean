-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_star_power_central_expansion
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.star_power_central_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:10:26.938304+00:00
-- url     : https://prove2.me/theorems/d2e8b629-67d3-424d-a26a-8557b1efb2e3
-- title:
--   Proposition 5.5
-- statement:
--   For every positive integer $k$, there is a finite rational central-character expansion of an observable $O_k$ of weight at most $k$ such that, as functions on all Young diagrams,
--
--   $$p_k^*=\sum_{\mathrm{wt}(\mu)=k+1}\frac{k^{\downarrow(\ell(\mu)-1)}}{\mathrm{fact}(\mu)}p_\mu^\sharp+O_k,\qquad O_k=\sum_{\mathrm{wt}(\mu)\le k}c_{k,\mu}p_\mu^\sharp.$$
--
--   Here $\mathrm{wt}(\mu)=|\mu|+\ell(\mu)$ and $\mathrm{fact}(\mu)=\prod_j m_j(\mu)!$. The remainder is computed by subtracting the displayed leading term. This separates the highest-weight and lower-weight contributions.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 47, Proposition 5.5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Proposition 5.5, arXiv:1501.05028v1, PDF p.47. Existence of rational coefficients is a conclusion, not a hypothesis. Equality is on every diagram, not a single shape. -/
theorem star_power_central_expansion
    (k : ℕ) (hk : 0 < k) :
    ∃ a : YoungDiagram →₀ ℚ,
      (∀ mu ∈ a.support, observableWeight mu ≤ k) ∧
      ∀ lambda : YoungDiagram,
        starPower k lambda = leading k lambda + observable a lambda ∧
        remainder k lambda = observable a lambda := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
