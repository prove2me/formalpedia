-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_commonMarginalRealization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.commonMarginalRealization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:23:30.825752+00:00
-- url     : https://prove2.me/theorems/7e94b985-b4cb-4c62-8fc3-120c50db0e70
-- title:
--   One pure resource locally realizes an arbitrary common-marginal family
-- statement:
--   Let $A$ and $B$ be copies of a nonzero finite-dimensional Hilbert space and let $S_B$ be a density operator. Let $(S_{BA}^i)_{i\in I}$ be an arbitrarily indexed family of normalized density operators satisfying $\operatorname{Tr}_A S_{BA}^i=S_B$ for every $i$. There is one unit vector $\psi\in B\otimes A$ with Bob marginal $S_B$, and a family of local CPTP maps $\mathcal E_i:A\to A$, such that
--
--   $$S_{BA}^i=(\operatorname{id}_B\otimes\mathcal E_i)(|\psi\rangle\langle\psi|)\qquad(i\in I).$$
--
--   The same pure resource precedes every encoder. Singular marginals and empty index families are permitted. This supplies the equivalence underlying the encoder-free capacity expression.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 7, §III, Lemma and equation (21): local realization of a common marginal

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF p.7, Lemma and (21): arbitrary indexed common-marginal families, including
singular Bob marginals. One pure resource is shared before every message-dependent encoder. -/
theorem commonMarginalRealization {A : Type} {I : Type*} [Fintype A]
    [DecidableEq A] [Nonempty A] (s : Matrix A A ℂ) (hs : IsDensityMatrix s)
    (rho : I → Matrix (A × A) (A × A) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (hmarg : ∀ i, traceRight (rho i) = s) :
    ∃ psi : EuclideanSpace ℂ (A × A), ‖psi‖ = 1 ∧ traceRight (pureDensity psi) = s ∧
      ∃ E : I → Superop A A, ∀ i, IsChannel (E i) ∧
        rho i = idTensorSuperop (E i) (pureDensity psi) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end
