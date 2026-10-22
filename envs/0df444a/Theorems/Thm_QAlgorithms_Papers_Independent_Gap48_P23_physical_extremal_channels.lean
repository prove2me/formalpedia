-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_physical_extremal_channels
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.physical_extremal_channels
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:40:21.883985+00:00
-- url     : https://prove2.me/theorems/85cae0c1-0156-4e2f-862f-458e83ecad0e
-- title:
--   Proposition 4.4.
-- statement:
--   For $\ell\ge1$, input covariance is with $T^\ell(U)$ and output covariance with $U$, for every $U\in U(2)$. The channel $\Phi_{\rm Tr}^\ell$ embeds through $V^\ell$ and keeps the first qubit; $\Phi_{\rm UNOT}^\ell$ measures the normalized coherent-state POVM and prepares the orthogonal state. Let $D_\ell$ be the explicit real dual Clebsch–Gordan matrix (C.49),(C.54). The unnormalized Choi order is output tensor input.
--
--   The two physically defined maps are channels:
--   $$\Phi_{\rm Tr}^\ell,\Phi_{\rm UNOT}^\ell\text{ are CPTP}\quad(\ell\ge1).$$
--   Their definitions apply to all input operators.
--
--   This characterizes the physical postprocessing maps used in the template algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 29, Proposition 4.4.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF pp.29-30, Proposition 4.4: the two Definition 4.3 maps are CPTP. -/
theorem physical_extremal_channels (ell : ℕ) (hell : 1 ≤ ell) :
    IsChannel (partialTraceChannel ell) ∧ IsChannel (universalNotChannel ell) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
