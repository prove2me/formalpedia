-- Prove2me | Theorems.Thm_WassKF_Reform_lemma_A_1
-- name    : WassKF.Reform.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:09:16.495024+00:00
-- url     : https://prove2.me/theorems/0308fc03-8f0b-4ea3-b132-14325c210508
-- title:
--   Lemma A.1 — $\sup_{S\succeq0}\langle D,S\rangle-\gamma\operatorname{Tr}[S-2(\Sigma^{1/2}S\Sigma^{1/2})^{1/2}]$ in closed form, with unique maximizer
-- statement:
--   Let $\gamma \ge 0$, let $D \in \mathbb S^d_+ \setminus \{0\}$ be a nonzero positive semidefinite matrix and let $\Sigma \in \mathbb S^d_{++}$ be positive definite. Write $\langle A, B \rangle = \operatorname{Tr}[A^\top B]$. Then
--
--   $$
--   \sup_{S \succeq 0} \; \langle D, S \rangle - \gamma \operatorname{Tr}\Bigl[S - 2\bigl(\Sigma^{1/2} S \Sigma^{1/2}\bigr)^{1/2}\Bigr]
--   = \begin{cases} \gamma^2 \bigl\langle (\gamma I_d - D)^{-1}, \Sigma \bigr\rangle & \text{if } \gamma I_d \succ D, \\ +\infty & \text{otherwise.} \end{cases}
--   $$
--
--   Moreover, if $\gamma I_d \succ D$, the unique optimal solution of the maximization problem is
--
--   $$
--   S^\star = \gamma^2 (\gamma I_d - D)^{-1} \Sigma (\gamma I_d - D)^{-1}.
--   $$
--
--   The lemma evaluates the inner maximization after the Wasserstein constraint is dualized, in the proof of Theorem 2.3.
--
--   **Formalization Note** The index set is an arbitrary finite type with decidable equality. The supremum is taken in `EReal`, so "$+\infty$" is `⊤`. The two cases are stated as two implications. "Unique optimal solution" is stated as: $S^\star$ is positive semidefinite and every other positive semidefinite $S$ has strictly smaller objective value; together with the value identity this says that $S^\star$ attains the supremum and is the only maximizer.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 9, Lemma A.1 (cited from Nguyen, Kuhn, Mohajerin Esfahani, Distributionally robust inverse covariance estimation, Proposition 2.8)

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_psdSqrt

open Matrix

namespace WassKF.Reform

/-- Lemma A.1 (cited from [18, Proposition 2.8]), Shafieezadeh-Abadeh et al.,
arXiv:1809.08830v3, p. 9. For `γ ≥ 0`, `D ∈ 𝕊^d_+ \ {0}` and `Sig ∈ 𝕊^d_{++}`,
`sup_{S ⪰ 0} ⟨D, S⟩ − γ Tr[S − 2 (Sig^{1/2} S Sig^{1/2})^{1/2}]` equals
`γ² ⟨(γ I − D)⁻¹, Sig⟩` if `γ I ≻ D` and `+∞` otherwise; and if `γ I ≻ D` the unique maximizer is
`S⋆ = γ² (γ I − D)⁻¹ Sig (γ I − D)⁻¹`. The trace inner product is `⟨A, B⟩ = Tr[Aᵀ B]`; the
supremum is taken in `EReal`. -/
theorem lemma_A_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (γ : ℝ) (hγ : 0 ≤ γ)
    (D Sig : Matrix ι ι ℝ) (hD : D.PosSemidef) (hD0 : D ≠ 0) (hSig : Sig.PosDef) :
    (¬ (γ • (1 : Matrix ι ι ℝ) - D).PosDef →
      (⨆ (S : Matrix ι ι ℝ) (_ : S.PosSemidef),
        (((Dᵀ * S).trace - γ * (S - (2 : ℝ) • WassersteinDRO.Shrinkage.psdSqrt
          (WassersteinDRO.Shrinkage.psdSqrt Sig * S * WassersteinDRO.Shrinkage.psdSqrt Sig)).trace
          : ℝ) : EReal)) = ⊤) ∧
    ((γ • (1 : Matrix ι ι ℝ) - D).PosDef →
      (⨆ (S : Matrix ι ι ℝ) (_ : S.PosSemidef),
        (((Dᵀ * S).trace - γ * (S - (2 : ℝ) • WassersteinDRO.Shrinkage.psdSqrt
          (WassersteinDRO.Shrinkage.psdSqrt Sig * S * WassersteinDRO.Shrinkage.psdSqrt Sig)).trace
          : ℝ) : EReal)) =
        ((γ ^ 2 * (((γ • (1 : Matrix ι ι ℝ) - D)⁻¹)ᵀ * Sig).trace : ℝ) : EReal) ∧
      (γ ^ 2 • ((γ • (1 : Matrix ι ι ℝ) - D)⁻¹ * Sig * (γ • (1 : Matrix ι ι ℝ) - D)⁻¹)).PosSemidef ∧
      ∀ S : Matrix ι ι ℝ, S.PosSemidef →
        S ≠ γ ^ 2 • ((γ • (1 : Matrix ι ι ℝ) - D)⁻¹ * Sig * (γ • (1 : Matrix ι ι ℝ) - D)⁻¹) →
        (Dᵀ * S).trace - γ * (S - (2 : ℝ) • WassersteinDRO.Shrinkage.psdSqrt
            (WassersteinDRO.Shrinkage.psdSqrt Sig * S * WassersteinDRO.Shrinkage.psdSqrt Sig)).trace <
          (Dᵀ * (γ ^ 2 • ((γ • (1 : Matrix ι ι ℝ) - D)⁻¹ * Sig * (γ • (1 : Matrix ι ι ℝ) - D)⁻¹))).trace -
            γ * (γ ^ 2 • ((γ • (1 : Matrix ι ι ℝ) - D)⁻¹ * Sig * (γ • (1 : Matrix ι ι ℝ) - D)⁻¹) -
              (2 : ℝ) • WassersteinDRO.Shrinkage.psdSqrt (WassersteinDRO.Shrinkage.psdSqrt Sig *
                (γ ^ 2 • ((γ • (1 : Matrix ι ι ℝ) - D)⁻¹ * Sig * (γ • (1 : Matrix ι ι ℝ) - D)⁻¹)) *
                WassersteinDRO.Shrinkage.psdSqrt Sig)).trace) := by sorry

end WassKF.Reform
