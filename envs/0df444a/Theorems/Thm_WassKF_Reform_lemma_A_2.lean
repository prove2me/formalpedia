-- Prove2me | Theorems.Thm_WassKF_Reform_lemma_A_2
-- name    : WassKF.Reform.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:09:19.029803+00:00
-- url     : https://prove2.me/theorems/edddbf42-331e-4641-b6de-c462b171621a
-- title:
--   Lemma A.2 — the direction-finding SDP is solved by $S^\star=(\gamma^\star)^2(\gamma^\star I-D)^{-1}\Sigma(\gamma^\star I-D)^{-1}$, and $S^\star\succeq\underline\sigma I$
-- statement:
--   Let $\Sigma \in \mathbb S^d_{++}$, let $D \in \mathbb S^d_+ \setminus \{0\}$, let $\rho > 0$, and let $\underline\sigma = \lambda_{\min}(\Sigma)$. Write $\langle A, B \rangle = \operatorname{Tr}[A^\top B]$. Consider the problem
--
--   $$
--   \sup_{S \in \mathbb S^d_+} \langle S, D \rangle \quad \text{s.t.} \quad \operatorname{Tr}\Bigl[S + \Sigma - 2\bigl(\Sigma^{1/2} S \Sigma^{1/2}\bigr)^{1/2}\Bigr] \le \rho^2 .
--   $$
--
--   1. There is a unique $\gamma^\star$ with $\gamma^\star I_d \succ D$ that solves the algebraic equation
--   $$
--   \rho^2 - \Bigl\langle \Sigma, \bigl(I_d - \gamma^\star(\gamma^\star I_d - D)^{-1}\bigr)^2 \Bigr\rangle = 0 .
--   $$
--   2. For this $\gamma^\star$, the matrix $S^\star = (\gamma^\star)^2 (\gamma^\star I_d - D)^{-1} \Sigma (\gamma^\star I_d - D)^{-1}$ is positive semidefinite, satisfies the constraint, and attains the supremum.
--   3. $S^\star \succeq \underline\sigma I_d$.
--
--   The lemma is used in the proof of Theorem 2.5 to show that the constraint $S \succeq \underline\sigma I_d$ of program (5) can be added without changing the optimal value.
--
--   **Formalization Note** The page states the lemma without a sign condition on $\rho$; the hypothesis $\rho > 0$ is added here because for $\rho = 0$ the algebraic equation has no root with $\gamma I_d \succ D$ (its second term is positive for every such $\gamma$), so item 1 would be false. $\underline\sigma$ is passed as a real number that is the least eigenvalue of $\Sigma$ (`IsLeast (Set.range eigenvalues) σ`). Item 2 is stated for every root $\gamma$ with $\gamma I_d \succ D$, which by item 1 is the root $\gamma^\star$. The index set is an arbitrary finite type with decidable equality.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 12, Lemma A.2

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_psdSqrt

open Matrix

namespace WassKF.Reform

/-- Lemma A.2 (Analytical solution of direction-finding subproblem), Shafieezadeh-Abadeh et al.,
arXiv:1809.08830v3, p. 12, with the radius `ρ > 0` made explicit (at `ρ = 0` the algebraic
equation has no root with `γ I ≻ D`). For `Sig ∈ 𝕊^d_{++}` and `D ∈ 𝕊^d_+ \ {0}`:
1. there is a unique `γ⋆` with `γ⋆ I ≻ D` and `ρ² − ⟨Sig, (I − γ⋆ (γ⋆ I − D)⁻¹)²⟩ = 0`;
2. for that `γ⋆`, `S⋆ = (γ⋆)² (γ⋆ I − D)⁻¹ Sig (γ⋆ I − D)⁻¹` is positive semidefinite, satisfies
   `Tr[S⋆ + Sig − 2 (Sig^{1/2} S⋆ Sig^{1/2})^{1/2}] ≤ ρ²`, and maximizes `⟨S, D⟩` over all
   positive semidefinite `S` satisfying that constraint;
3. `S⋆ ⪰ σ I`, where `σ = λ_min(Sig)`.
The trace inner product is `⟨A, B⟩ = Tr[Aᵀ B]`. -/
theorem lemma_A_2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Sig D : Matrix ι ι ℝ) (hSig : Sig.PosDef) (hD : D.PosSemidef) (hD0 : D ≠ 0)
    (ρ : ℝ) (hρ : 0 < ρ) (σ : ℝ) (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ) :
    (∃! γ : ℝ, (γ • (1 : Matrix ι ι ℝ) - D).PosDef ∧
        ρ ^ 2 - (Sigᵀ * ((1 : Matrix ι ι ℝ) - γ • (γ • (1 : Matrix ι ι ℝ) - D)⁻¹) ^ 2).trace = 0) ∧
    ∀ γ : ℝ, (γ • (1 : Matrix ι ι ℝ) - D).PosDef →
      ρ ^ 2 - (Sigᵀ * ((1 : Matrix ι ι ℝ) - γ • (γ • (1 : Matrix ι ι ℝ) - D)⁻¹) ^ 2).trace = 0 →
      (γ ^ 2 • ((γ • (1 : Matrix ι ι ℝ) - D)⁻¹ * Sig * (γ • (1 : Matrix ι ι ℝ) - D)⁻¹)).PosSemidef ∧
      (γ ^ 2 • ((γ • (1 : Matrix ι ι ℝ) - D)⁻¹ * Sig * (γ • (1 : Matrix ι ι ℝ) - D)⁻¹) + Sig -
          (2 : ℝ) • WassersteinDRO.Shrinkage.psdSqrt (WassersteinDRO.Shrinkage.psdSqrt Sig *
            (γ ^ 2 • ((γ • (1 : Matrix ι ι ℝ) - D)⁻¹ * Sig * (γ • (1 : Matrix ι ι ℝ) - D)⁻¹)) *
            WassersteinDRO.Shrinkage.psdSqrt Sig)).trace ≤ ρ ^ 2 ∧
      (∀ S : Matrix ι ι ℝ, S.PosSemidef →
        (S + Sig - (2 : ℝ) • WassersteinDRO.Shrinkage.psdSqrt (WassersteinDRO.Shrinkage.psdSqrt Sig *
          S * WassersteinDRO.Shrinkage.psdSqrt Sig)).trace ≤ ρ ^ 2 →
        (Sᵀ * D).trace ≤
          ((γ ^ 2 • ((γ • (1 : Matrix ι ι ℝ) - D)⁻¹ * Sig * (γ • (1 : Matrix ι ι ℝ) - D)⁻¹))ᵀ * D).trace) ∧
      (γ ^ 2 • ((γ • (1 : Matrix ι ι ℝ) - D)⁻¹ * Sig * (γ • (1 : Matrix ι ι ℝ) - D)⁻¹) -
        σ • (1 : Matrix ι ι ℝ)).PosSemidef := by sorry

end WassKF.Reform
