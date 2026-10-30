-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_rank_tester_pointwise_optimal
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.rank_tester_pointwise_optimal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:18:17.978981+00:00
-- url     : https://prove2.me/theorems/75e17ab7-3e03-4a31-8e06-92cc79ee8e64
-- title:
--   Proposition 6.1
-- statement:
--   Fix $d\ge r\ge1$ and $n\ge0$. Any collective $n$-copy effect $M$ that accepts every state of rank at most $r$ with probability one has, on every input density matrix $\rho$,
--
--   $$\Pr[\text{Rank Tester accepts }\rho]\le\Pr[M\text{ accepts }\rho].$$
--
--   The Rank Tester itself accepts every rank-at-most-$r$ input with probability one. Hence it maximizes rejection probability pointwise among perfectly complete testers, with no asymptotic qualification.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 56, Proposition 6.1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Proposition 6.1, arXiv:1501.05028v1, PDF p.56. Pointwise optimality, not only copy-complexity equality. Perfect completeness for every basis forces acceptance on the entire low-height isotypic subspace. -/
theorem rank_tester_pointwise_optimal
    (d n r : ℕ) (hd : 0 < d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (M : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (hM : IsEffect M)
    (hcomplete : ∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
      decreasingSpectrum rho ∈ supportProperty d r → effectProb M (piKron n rho) = 1) :
    (∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
      decreasingSpectrum rho ∈ supportProperty d r → rankAccept n r rho = 1) ∧
    ∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
      rankAccept n r rho ≤ effectProb M (piKron n rho) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
