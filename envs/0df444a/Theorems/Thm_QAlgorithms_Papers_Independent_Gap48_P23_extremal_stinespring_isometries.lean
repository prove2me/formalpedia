-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_extremal_stinespring_isometries
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.extremal_stinespring_isometries
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:08:30.532552+00:00
-- url     : https://prove2.me/theorems/ff2d7cd0-0b25-4669-9580-be271fc2e362
-- title:
--   Lemma E.5.
-- statement:
--   For $\ell\ge1$, input covariance is with $T^\ell(U)$ and output covariance with $U$, for every $U\in U(2)$. The channel $\Phi_{\rm Tr}^\ell$ embeds through $V^\ell$ and keeps the first qubit; $\Phi_{\rm UNOT}^\ell$ measures the normalized coherent-state POVM and prepares the orthogonal state. Let $D_\ell$ be the explicit real dual Clebsch–Gordan matrix (C.49),(C.54). The unnormalized Choi order is output tensor input.
--
--   For $\ell\ge1$, the channel isometries are
--   $$U_{\rm Tr}|v\rangle=\sqrt{(\ell-v)/\ell}|0,v\rangle+\sqrt{v/\ell}|1,v-1\rangle,$$
--   $$U_{\rm UNOT}|w\rangle=-\sqrt{(w+1)/(\ell+2)}|0,w+1\rangle+\sqrt{(\ell+1-w)/(\ell+2)}|1,w\rangle.$$
--   Both obey $U^\dagger U=I$, and tracing their environments gives the physical channels on every operator. Zero-coefficient boundary kets are omitted.
--
--   This characterizes the physical postprocessing maps used in the template algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 77, Lemma E.5.

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

/-- PDF pp.77-78, Lemma E.5: exact source isometries, including the UNOT
minus phase relative to the accepted library upper isometry. -/
theorem extremal_stinespring_isometries (ell : ℕ) (hell : 1 ≤ ell) :
    (traceIsometry ell)ᴴ * traceIsometry ell = 1 ∧
    (notIsometry ell)ᴴ * notIsometry ell = 1 ∧
    (∀ rho, partialTraceChannel ell rho = traceRight (traceIsometry ell * rho * (traceIsometry ell)ᴴ)) ∧
    (∀ rho, universalNotChannel ell rho = traceRight (notIsometry ell * rho * (notIsometry ell)ᴴ)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
