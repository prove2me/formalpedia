-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P95_perfect_code_to_perfect_state
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P95.perfect_code_to_perfect_state
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:47:52.956674+00:00
-- url     : https://prove2.me/theorems/58180390-d693-44a7-b4f0-4c5f9d4fdad0
-- title:
--   A maximum-erasure-protection code gives a perfect state
-- statement:
--   Let $n\ge1$, $v\ge2$, and let $M$ be an isometry encoding one $v$-dimensional spin into $2n-1$ physical spins of dimension $v$. For every erased set of at most $n-1$ physical spins, assume there is one CPTP recovery channel, chosen independently of the logical input, that exactly recovers all logical density matrices (equivalently all operators by linearity). Add a reference spin and construct
--
--   $$\lvert\Psi_M\rangle=\frac1{\sqrt v}\sum_{j=0}^{v-1}M\lvert j\rangle\otimes\lvert j\rangle.$$
--
--   Then this vector is normalized and perfect. For every subset $A$ of at most $n$ of its $2n$ spins,
--
--   $$\rho_A=I_A/v^{|A|}.$$
--
--   This is the maximum-erasure-protection meaning of perfect code from the surrounding discussion on p.8. Neither purity nor maximally mixed physical marginals are assumed.
-- source:
--   Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence, arXiv:1503.06237v2, PDF p. 45, Appendix A.1: perfect code to perfect state

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P95

namespace QAlgorithms.Papers.Independent.Intakenext100.P95

open scoped Matrix ComplexConjugate

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- PDF pp.8,45, Appendix A.1: the normalized Choi state of an isometric
[[2n−1,1,n]]_v maximum-erasure-protection code is a perfect 2n-spin state.
The assumptions require exact correction of n−1 erasures. In particular, no
maximally mixed physical marginal or purity conclusion is assumed. -/
theorem perfect_code_to_perfect_state {L V : Type*} [Fintype L] [Fintype V]
    [DecidableEq L] [DecidableEq V] (n : ℕ) (hn : 1 ≤ n)
    (hlegs : Fintype.card L = 2 * n - 1) (hv : 2 ≤ Fintype.card V)
    (M : Matrix (L → V) V ℂ) (hcode : IsPerfectErasureCode n M) :
    IsState (encoderPurification M) ∧ IsPerfect (encoderPurification M) ∧
    ∀ A : Finset (L ⊕ Unit), A.card ≤ n →
      subsetDensity A (pureDensity (encoderPurification M)) = ((Fintype.card (SubsetConfig V A) : ℂ)⁻¹ • 1) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P95
