-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P22_squashed_traceNormFaithfulness
-- name    : QAlgorithms.Papers.Independent.Gap48.P22.squashed_traceNormFaithfulness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:14:49.932528+00:00
-- url     : https://prove2.me/theorems/9943e4f0-6989-4865-9693-ff02c61ec04f
-- title:
--   Trace-norm faithfulness of squashed entanglement
-- statement:
--   Let $\rho^{AB}$ be a density operator on finite positive-dimensional systems, with bit-valued squashed entanglement $E_{\rm sq}(\rho)\le\varepsilon$ and $\varepsilon\ge0$. There is a separable density operator $\sigma^{AB}$ such that
--
--   $$\|\rho-\sigma\|_1\le\frac{31}{10}\,\dim(B)\,\varepsilon^{1/4}.$$
--
--   Moreover,
--
--   $$E_{\rm sq}(\rho)=0\quad\Longleftrightarrow\quad\rho\text{ is separable}.$$
--
--   Here $\|\cdot\|_1$ is the full trace norm and squashed entanglement takes the half-infimum over every finite extension dimension. The conclusion supplies an actual separable witness, including at $\varepsilon=0$.
-- source:
--   Squashed entanglement, k-extendibility, quantum Markov chains, and recovery maps, arXiv:1410.4184v4, PDF p. 3, Corollary 1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Gap48.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P12 (squashedEntanglement KExtendible)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (RegisterBasis registerMarginal entropyAt conditionalMultipartiteInformation singleParties
   forgetEnvironment)

open QAlgorithms.Papers.Independent.Renew46.P35 (classicalCMI)

open QAlgorithms.Entanglement (IsSeparableDensity)

/-- Corollary 1, PDF pp.3–4: the attained separable witness, constant 3.1=31/10,
and the complete zero-if-and-only-if-separable clause. -/
theorem squashed_traceNormFaithfulness {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hsmall : squashedEntanglement rho ≤ epsilon) :
    (∃ sigma : Matrix (A × B) (A × B) ℂ, IsDensityMatrix sigma ∧ IsSeparableDensity sigma ∧
      traceNorm (rho-sigma) ≤ (31/10 : ℝ) * (Fintype.card B : ℝ) *
        Real.sqrt (Real.sqrt epsilon)) ∧
    (squashedEntanglement rho = 0 ↔ IsSeparableDensity rho) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P22

end
