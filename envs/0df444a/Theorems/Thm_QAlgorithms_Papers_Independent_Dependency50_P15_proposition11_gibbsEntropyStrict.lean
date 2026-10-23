-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P15_proposition11_gibbsEntropyStrict
-- name    : QAlgorithms.Papers.Independent.Dependency50.P15.proposition11_gibbsEntropyStrict
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:26:27.280954+00:00
-- url     : https://prove2.me/theorems/e06d7d87-1778-421d-93c1-d533744117ee
-- title:
--   Proposition 11: strict increase and strict concavity of Gibbs entropy
-- statement:
--   Let $H$ be a self-adjoint Hamiltonian on an infinite-dimensional separable complex Hilbert space, with discrete spectrum, ground energy zero, and $\operatorname{Tr}e^{-\beta H}<\infty$ for every $\beta>0$. For every finite energy budget $E\ge0$, let $\gamma(E)$ be its constructed maximum-entropy state under $\operatorname{Tr}\rho H\le E$: at $E>0$ it has Gibbs weights with mean energy $E$, and at $E=0$ it is the normalized ground-space projector. Then
--
--   $$E\longmapsto S(\gamma(E))\quad\text{is strictly increasing and strictly concave on }[0,\infty).$$
--
--   Entropy is measured in bits and eigenvalues are counted with multiplicity. These two strict properties describe the energy dependence of the thermal entropy.
--
--   **Formalization Note** The full countably infinite eigenvalue list represents $H$ in an orthonormal eigenbasis. Its Gibbs probabilities and inverse temperature are computed from that list. The source credits Shirokov [37, Proposition 1] and supplies a proof.
-- source:
--   Tight uniform continuity bounds for quantum entropies: conditional entropy, relative entropy distance and energy constraints, arXiv:1507.07775v6, PDF p. 7, Proposition 11: strict increase and strict concavity of Gibbs entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P15

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P15

open QAlgorithms.Papers.Independent.Information100.P08 (bellVector)

/-- Proposition 11, PDF p.7: BOTH strict properties on all finite nonnegative budgets.
The full countably infinite spectrum represents the entire separable Hilbert space.
The Gibbs state is constructed from that spectrum; it is not an arbitrary optimizer.
The source credits Shirokov [37, Prop.1] and provides its own proof. -/
theorem proposition11_gibbsEntropyStrict {I : Type*} [Countable I] [Infinite I]
    (energy : I → ℝ) (hGibbs : IsGibbsSpectrum energy) :
    StrictMonoOn (gibbsEntropy energy) (Set.Ici 0) ∧
      StrictConcaveOn ℝ (Set.Ici 0) (gibbsEntropy energy) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P15

end
