-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_extremal_physical_identification
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.extremal_physical_identification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:07:44.992445+00:00
-- url     : https://prove2.me/theorems/0dd61de4-7d73-459f-ad1c-98b7db5ed747
-- title:
--   Lemma E.4.
-- statement:
--   For $\ell\ge1$, input covariance is with $T^\ell(U)$ and output covariance with $U$, for every $U\in U(2)$. The channel $\Phi_{\rm Tr}^\ell$ embeds through $V^\ell$ and keeps the first qubit; $\Phi_{\rm UNOT}^\ell$ measures the normalized coherent-state POVM and prepares the orthogonal state. Let $D_\ell$ be the explicit real dual Clebsch–Gordan matrix (C.49),(C.54). The unnormalized Choi order is output tensor input.
--
--   For every $\ell\ge1$, the exact endpoint identifications are
--   $$\Phi_1^\ell=\Phi_{\rm Tr}^\ell,\qquad\Phi_2^\ell=\Phi_{\rm UNOT}^\ell.$$
--   Equality holds on all operators, not just coherent states.
--
--   This characterizes the physical postprocessing maps used in the template algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 75, Lemma E.4.

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

/-- PDF p.75, Lemma E.4: exact identities of linear maps on all operators. -/
theorem extremal_physical_identification (ell : ℕ) (hell : 1 ≤ ell) :
    extremalChannel ell false = partialTraceChannel ell ∧
    extremalChannel ell true = universalNotChannel ell := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
