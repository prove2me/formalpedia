-- Prove2me | Theorems.Thm_PDASNewton_NormCone_merit_bound_3_7
-- name    : PDASNewton.NormCone.merit_bound_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:39.074621+00:00
-- url     : https://prove2.me/theorems/7af04b3b-5c65-437d-be09-4f9573b02cae
-- title:
--   (3.7), p. 8 — Σᵢ(yᵏ⁺¹ᵢ − yᵏᵢ) ≤ −‖yᵏ − ψ‖_{1,𝓐ₖ} + ‖(A_𝓘ₖ⁻¹A_𝓘ₖ𝓐ₖ)₊‖₁ ‖yᵏ − ψ‖_{1,𝓐ₖ} (the inequality)
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be a P-matrix, $f, \psi \in \mathbb{R}^n$ and $c > 0$, and assume the cone condition of Theorem 3.3: $\sum_{i\in\mathcal{I}} (A_{\mathcal{I}}^{-1} v)_i \ge 0$ for every index set $\mathcal{I}$ and every $v \ge 0$ in $\mathbb{R}^{|\mathcal{I}|}$. Let $(y^k, \lambda^k)_{k\ge 0}$ be a run of the primal-dual active set algorithm, and for $k\ge1$ let $\mathcal{I}_k$, $\mathcal{A}_k$ be the inactive and active sets of $(y^k, \lambda^k)$. Write $\|w\|_{1,\mathcal{A}} = \sum_{i\in\mathcal{A}} |w_i|$, and $\|B_+\|_1$ for the maximal column sum of the positive part of a matrix $B$. Then
--   $$\sum_{i=1}^n (y^{k+1}_i - y^k_i) \le -\|y^k - \psi\|_{1,\mathcal{A}_k} + \big\|(A_{\mathcal{I}_k}^{-1} A_{\mathcal{I}_k\mathcal{A}_k})_+\big\|_1 \, \|y^k - \psi\|_{1,\mathcal{A}_k}.$$
--
--   Under the norm condition $\|(A_{\mathcal{I}}^{-1}A_{\mathcal{I}\mathcal{A}})_+\|_1 < 1$ of Theorem 3.3 the right-hand side is $\le 0$, so $\mathcal{M}(y) = \sum_i y_i$ does not increase along the iterates from $k = 1$ on.
--
--   **Formalization Note** This item is the inequality of (3.7) only. The page continues "$< 0$, unless $y^{k+1} = y^k$"; that strict part is not stated here, because it does not follow from (3.6)–(3.7) as written (the right-hand side vanishes when $y^k = \psi$ on $\mathcal{A}_k$, while $y^{k+1} \neq y^k$ remains possible). The norm condition is not a hypothesis of this item. $c > 0$ is the paper's standing assumption.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 8, proof of Theorem 3.3, (3.7)

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting
import Definitions.Def_PDASNewton_NormCone_Setting

open Filter Topology Matrix

namespace PDASNewton.NormCone

theorem merit_bound_3_7 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : RobinsonSR.Schur.IsPMatrix A)
    (hcone : ∀ S : Finset (Fin n), ∀ v : S → ℝ, 0 ≤ v → 0 ≤ ∑ i, ((PDASNewton.MMatrix.principal A S)⁻¹ *ᵥ v) i)
    (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, 1 ≤ k → ∀ S : Finset (Fin n), S = (PDASNewton.Local.activeSet c ψ (y k) (lam k))ᶜ →
      ∑ i, (y (k + 1) i - y k i) ≤
        -∑ i ∈ Sᶜ, |y k i - ψ i| +
          posPartOneNorm ((PDASNewton.MMatrix.principal A S)⁻¹ * PDASNewton.MMatrix.offDiag A S) * ∑ i ∈ Sᶜ, |y k i - ψ i| := by sorry

end PDASNewton.NormCone
