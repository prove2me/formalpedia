-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_extremal_kraus_operators
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.extremal_kraus_operators
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:05:40.241121+00:00
-- url     : https://prove2.me/theorems/42ff3a6a-c7b0-419c-be94-aa4fb56f666f
-- title:
--   Lemma E.1 (Kraus operators for Φ1` and Φ2` ).
-- statement:
--   For $\ell\ge1$, input covariance is with $T^\ell(U)$ and output covariance with $U$, for every $U\in U(2)$. The channel $\Phi_{\rm Tr}^\ell$ embeds through $V^\ell$ and keeps the first qubit; $\Phi_{\rm UNOT}^\ell$ measures the normalized coherent-state POVM and prepares the orthogonal state. Let $D_\ell$ be the explicit real dual Clebsch–Gordan matrix (C.49),(C.54). The unnormalized Choi order is output tensor input.
--
--   For $\ell\ge1$, the endpoint Kraus families are
--   $$K_v^{\rm Tr}=\sqrt{\frac{\ell-v}{\ell}}|0\rangle\langle v|+\sqrt{\frac{v+1}{\ell}}|1\rangle\langle v+1|,\quad0\le v<\ell,$$
--   $$K_w^{\rm UNOT}=-\sqrt{\frac w{\ell+2}}|0\rangle\langle w-1|+\sqrt{\frac{\ell+1-w}{\ell+2}}|1\rangle\langle w|,\quad0\le w\le\ell+1.$$
--   They are normalized and realize the exact D-based channels. Undefined boundary bras are omitted; the two endpoints are $\sqrt{(\ell+1)/(\ell+2)}|1\rangle\langle0|$ and its negatively phased $|0\rangle\langle\ell|$ counterpart.
--
--   This characterizes the physical postprocessing maps used in the template algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 73, Lemma E.1 (Kraus operators for Φ1` and Φ2` ).

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

/-- PDF pp.73-74, Lemma E.1: full Kraus families, normalization, and both
UNOT endpoints, with invalid boundary bras omitted. -/
theorem extremal_kraus_operators (ell : ℕ) (hell : 1 ≤ ell) :
    IsKrausFamily (traceKraus ell) ∧ IsKrausFamily (notKraus ell) ∧
    extremalChannel ell false = krausApply (traceKraus ell) ∧
    extremalChannel ell true = krausApply (notKraus ell) ∧
    notKraus ell 0 = (Real.sqrt (((ell : ℝ)+1)/(ell+2)) : ℂ) • Matrix.single 1 0 1 ∧
    notKraus ell ⟨ell+1, by omega⟩ =
      -(Real.sqrt (((ell : ℝ)+1)/(ell+2)) : ℂ) • Matrix.single 0 ⟨ell, by omega⟩ 1 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
