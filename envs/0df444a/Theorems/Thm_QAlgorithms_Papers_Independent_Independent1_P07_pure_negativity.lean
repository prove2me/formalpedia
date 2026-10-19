-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_pure_negativity
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.pure_negativity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:47:59.576316+00:00
-- url     : https://prove2.me/theorems/55bec2d6-5ce6-4cf1-a89a-316f33449dde
-- title:
--   Pure-state negativity and robustness
-- statement:
--   Let $|\psi\rangle=\sum_i c_i|u_i\rangle\otimes|v_i\rangle$ be a Schmidt expansion, where the two vector families are orthonormal, $c_i\ge0$, and $\sum_i c_i^2=1$. For $\rho=|\psi\rangle\langle\psi|$,
--
--   $$N(\rho)=\frac{(\sum_i c_i)^2-1}2,\qquad N_{ss}(\rho)=2N(\rho).$$
--
--   Coefficients are amplitudes, not squared eigenvalues; zero padding and rectangular local spaces are allowed. The robustness identification retains the source's attribution to [18].
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §V.A, Proposition 8, Eq. (48), PDF p. 7. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false

/-! Vidal–Werner, arXiv:quant-ph/0102117v1. All locators are PDF pages.
Paper-local operational and variational definitions precede their statements.
Deferred source inconsistencies and interfaces are recorded in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P07

open Entanglement







































/-- Proposition 8, Eq. (48), PDF p. 7, including the robustness relation attributed to [18]. -/
theorem pure_negativity {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J]
    {r : ℕ} (c : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ I)
    (v : Fin r → EuclideanSpace ℂ J) (hc : ∀ i, 0 ≤ c i)
    (hs : ∑ i, c i^2 = 1) (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) :
    let rho := pureDensity (schmidtState c u v)
    negativity rho = ((∑ i, c i)^2-1)/2 ∧ separableRobustness rho = 2*negativity rho := by sorry

























end QAlgorithms.Papers.Independent.Independent1.P07
