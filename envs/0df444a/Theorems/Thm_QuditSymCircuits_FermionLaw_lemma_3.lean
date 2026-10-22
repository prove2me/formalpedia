-- Prove2me | Theorems.Thm_QuditSymCircuits_FermionLaw_lemma_3
-- name    : QuditSymCircuits.FermionLaw.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:50.155788+00:00
-- url     : https://prove2.me/theorems/e6c673c7-e7c2-409f-bcce-153d6972a237
-- title:
--   Lemma 3, p. 11 — covariance Ω[e^{iθP_ab}ρe^{−iθP_ab}] = e^{iθE_ab}Ω[ρ]e^{−iθE_ab} and complete positivity of Ω
-- statement:
--   The linear map $\Omega$ of Eqs. (49) and (51) satisfies
--
--   1. the covariance condition
--   $$\Omega\big[e^{i\theta\mathbf P_{ab}}\,\rho\,e^{-i\theta\mathbf P_{ab}}\big] = e^{i\theta E_{ab}}\,\Omega[\rho]\,e^{-i\theta E_{ab}}$$
--   for every operator $\rho$ on $(\mathbb C^d)^{\otimes n}$, every $\theta\in[0,2\pi)$ and every pair of sites $a,b$, where $E_{ab}$ is the single-particle swap of Eq. (33);
--   2. $\Omega$ is completely positive: for every $r$, $\mathrm{id}_r\otimes\Omega$ maps positive semidefinite operators to positive semidefinite operators.
--
--   The covariance turns each 2-local SU(d)-invariant gate into a unitary conjugation of the $n\times n$ matrix $\Omega[\rho]$, which is what Theorem 2 needs.
--
--   **Formalization Note.** Exponentials are in the closed form $\cos\theta\,\mathbb I\pm i\sin\theta\,X$ of Eq. (5). Complete positivity is the published `QAlgorithms.Entanglement.IsCompletelyPositive`. $a = b$ is allowed.
-- source:
--   Marvian, Liu and Hulse, Qudit circuits with SU(d) symmetry, arXiv:2105.12877v2, p. 11, Lemma 3, Eq. (53); proof App. C8, pp. 33–34

import Mathlib
import Definitions.Def_QuditSymCircuits_FermionLaw_Model

open scoped Matrix
open QuditSymCircuits.FermionLaw QAlgorithms.Entanglement

namespace QuditSymCircuits.FermionLaw

theorem lemma_3 (n d : ℕ) [NeZero d] :
    (∀ θ : ℝ, θ ∈ Set.Ico 0 (2 * Real.pi) → ∀ a b : Fin n, ∀ ρ : Op n d,
      omega n d (expInv θ (swapOp a b : Op n d) * ρ * expInv (-θ) (swapOp a b : Op n d)) =
        expInv θ (Eab a b) * omega n d ρ * expInv (-θ) (Eab a b)) ∧
    IsCompletelyPositive (omega n d) := by sorry

end QuditSymCircuits.FermionLaw
