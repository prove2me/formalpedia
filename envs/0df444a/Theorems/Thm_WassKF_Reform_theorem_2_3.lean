-- Prove2me | Theorems.Thm_WassKF_Reform_theorem_2_3
-- name    : WassKF.Reform.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:13:12.142886+00:00
-- url     : https://prove2.me/theorems/3bb5109c-3a1a-476f-a4d7-e9fecfdb91be
-- title:
--   Theorem 2.3 — minimax theorem (4) for MMSE estimation over the Gaussian Wasserstein ball
-- statement:
--   Let $\mathbb P = \mathcal N_d(\mu, \Sigma)$ with $\Sigma \succ 0$, let $\rho \ge 0$, and let $\mathcal P = \{\mathbb Q \in \mathcal N_d : W_2(\mathbb Q, \mathbb P) \le \rho\}$ be the Wasserstein ambiguity set (3) of normal distributions. Let $\mathcal L$ be the family of all measurable functions $\psi : \mathbb R^m \to \mathbb R^n$. Then
--
--   $$
--   \inf_{\psi \in \mathcal L} \sup_{\mathbb Q \in \mathcal P} \mathbb E^{\mathbb Q}\bigl[\|x - \psi(y)\|^2\bigr] = \sup_{\mathbb Q \in \mathcal P} \inf_{\psi \in \mathcal L} \mathbb E^{\mathbb Q}\bigl[\|x - \psi(y)\|^2\bigr].
--   $$
--
--   The ambiguity set is not convex, so the equality does not follow from Sion's minimax theorem. It says that the statistician choosing $\psi$ and nature choosing $\mathbb Q$ have the same value in the zero-sum game behind problem (2).
--
--   **Formalization Note** Both sides are the definitions `minimaxValue` and `maximinValue`, valued in $[0,\infty]$. The hypotheses $\Sigma \succ 0$ and $\rho \ge 0$ are the standing assumptions stated with (3) on p. 3.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 3, Theorem 2.3, (4)

import Mathlib
import Definitions.Def_WassKF_Reform_minimaxValue
import Definitions.Def_WassKF_Reform_maximinValue

namespace WassKF.Reform

/-- Theorem 2.3 (Minimax theorem), Shafieezadeh-Abadeh et al., arXiv:1809.08830v3, p. 3, eq. (4):
for the Wasserstein ambiguity set (3) of normal distributions around `ℙ = 𝒩_d(μ, Sig)` with
`Sig ≻ 0` and radius `ρ ≥ 0`,
`inf_{ψ ∈ ℒ} sup_{Q ∈ 𝒫} E^Q[‖x − ψ(y)‖²] = sup_{Q ∈ 𝒫} inf_{ψ ∈ ℒ} E^Q[‖x − ψ(y)‖²]`. -/
theorem theorem_2_3 {n m : ℕ} (μ : EuclideanSpace ℝ (Fin n ⊕ Fin m))
    (Sig : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (hSig : Sig.PosDef)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    minimaxValue μ Sig ρ = maximinValue μ Sig ρ := by sorry

end WassKF.Reform
