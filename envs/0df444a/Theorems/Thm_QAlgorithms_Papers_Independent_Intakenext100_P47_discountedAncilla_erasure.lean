-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P47_discountedAncilla_erasure
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P47.discountedAncilla_erasure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:14:27.851453+00:00
-- url     : https://prove2.me/theorems/695011b4-130c-4ffd-a7f4-621965477842
-- title:
--   Section II, discounted ancillary correlation does not change total erasure cost
-- statement:
--   Fix a density matrix $\rho_{AB}$ on finite nonzero complex spaces. Allow an arbitrary ancillary bipartite density matrix $\gamma_{CD}$, with finite nonzero ancillary dimensions. Regroup $\rho\otimes\gamma$ as $AC:BD$ and let $C_{\rm er}$ be the operational total-erasure rate computed from product-unitary noise ensembles. Every discounted cost has the same value, and hence
--
--   $$\{C_{\rm er}(\rho\otimes\gamma)-C_{\rm er}(\gamma):\gamma_{CD}\text{ as above}\}=\{I(A:B)_\rho\},\qquad\inf_\gamma\bigl(C_{\rm er}(\rho\otimes\gamma)-C_{\rm er}(\gamma)\bigr)=I(A:B)_\rho.$$
--
--   The ancillary correlation is erased and its erasure cost discounted. This describes the ancillary-cost observation in Section II; no return of an unchanged catalyst is required.
-- source:
--   On the quantum, classical and total amount of correlations in a quantum state, arXiv:quant-ph/0410091v2, PDF p. 5, Section II, discounted ancillary correlation does not change total erasure cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P47

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies localProduct)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon Config)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, ancillary-cost paragraph: erasing and discounting the ancillary correlation. -/
theorem discountedAncilla_erasure {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) :
    discountedCosts rho = {mutualInformation rho} ∧
    sInf (discountedCosts rho) = mutualInformation rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P47

end
