-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P15_corollary12_gibbsPerspective
-- name    : QAlgorithms.Papers.Independent.Dependency50.P15.corollary12_gibbsPerspective
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:27:20.328707+00:00
-- url     : https://prove2.me/theorems/ca423c3b-af82-4846-8fc6-2a6b6ea8aae9
-- title:
--   Corollary 12: attained supremum of the Gibbs entropy perspective
-- statement:
--   Let $H$ satisfy the discrete-spectrum Gibbs hypotheses of Proposition 11 on an infinite-dimensional separable Hilbert space, and let $\gamma(E)$ denote the Gibbs state constructed at energy budget $E\ge0$, including the normalized ground-space state at zero. For every finite $E\ge0$ and every real $\delta>0$, the set below is nonempty and bounded above, and its supremum is attained at $\lambda=\delta$:
--
--   $$\sup_{0<\lambda\le\delta}\lambda S\!\left(\gamma(E/\lambda)\right)=\delta S\!\left(\gamma(E/\delta)\right).$$
--
--   All entropies are in bits. The parameter $\delta$ has no upper probability restriction. This identifies the exact maximum of the entropy perspective over the stated interval.
-- source:
--   Tight uniform continuity bounds for quantum entropies: conditional entropy, relative entropy distance and energy constraints, arXiv:1507.07775v6, PDF p. 7, Corollary 12: attained supremum of the Gibbs entropy perspective

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P15

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P15

open QAlgorithms.Papers.Independent.Information100.P08 (bellVector)

/-- Corollary 12, PDF p.7: the supremum over 0<lambda≤delta is attained at delta.
Nonemptiness and finite upper boundedness explicitly guard the real supremum.
E=0 and ground-space degeneracy are included; delta need not be a probability. -/
theorem corollary12_gibbsPerspective {I : Type*} [Countable I] [Infinite I]
    (energy : I → ℝ) (hGibbs : IsGibbsSpectrum energy)
    (E delta : ℝ) (hE : 0 ≤ E) (hdelta : 0 < delta) :
    let values := {v : ℝ | ∃ lambda : ℝ, 0 < lambda ∧ lambda ≤ delta ∧
      v = lambda * gibbsEntropy energy (E / lambda)}
    values.Nonempty ∧ BddAbove values ∧
      delta * gibbsEntropy energy (E / delta) ∈ values ∧
      sSup values = delta * gibbsEntropy energy (E / delta) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P15

end
