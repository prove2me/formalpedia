-- Prove2me | Theorems.Thm_PDASNewton_NormCone_sum_decrease_3_6
-- name    : PDASNewton.NormCone.sum_decrease_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:40.185623+00:00
-- url     : https://prove2.me/theorems/3a2709e4-529a-44bd-ae49-37a981d93fa2
-- title:
--   (3.6), p. 8 — Σᵢ(yᵏ⁺¹ᵢ − yᵏᵢ) ≤ −Σ_𝓐ₖ(yᵏᵢ − ψᵢ) + Σ_𝓘ₖ(A_𝓘ₖ⁻¹A_𝓘ₖ𝓐ₖ(yᵏ − ψ)_𝓐ₖ)ᵢ under the cone condition
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be a P-matrix, $f, \psi \in \mathbb{R}^n$ and $c > 0$. Assume the cone condition of Theorem 3.3: for every index set $\mathcal{I}$ and every $v \in \mathbb{R}^{|\mathcal{I}|}$ with $v \ge 0$,
--   $$\sum_{i \in \mathcal{I}} (A_{\mathcal{I}}^{-1} v)_i \ge 0.$$
--   Let $(y^k, \lambda^k)_{k\ge0}$ be a run of the primal-dual active set algorithm, and for $k \ge 1$ let $\mathcal{I}_k$, $\mathcal{A}_k$ be the inactive and active sets of $(y^k,\lambda^k)$ (calligraphic $\mathcal{A}$ is an index set, $A$ the matrix). Then
--   $$\sum_{i=1}^n (y^{k+1}_i - y^k_i) \le -\sum_{i\in\mathcal{A}_k} (y^k_i - \psi_i) + \sum_{i \in \mathcal{I}_k} \big(A_{\mathcal{I}_k}^{-1} A_{\mathcal{I}_k\mathcal{A}_k} (y^k - \psi)_{\mathcal{A}_k}\big)_i.$$
--
--   This is inequality (3.6): it bounds the change of the merit function $\mathcal{M}(y) = \sum_i y_i$ over one step by a quantity that the norm condition of Theorem 3.3 controls.
--
--   **Formalization Note** The cone condition is quantified over every `S : Finset (Fin n)`, including $\emptyset$ and the full index set, as on the page ("for every partitioning"). $c > 0$ is the paper's standing assumption; it enters through the sign fact $\lambda^k_{\mathcal{I}_k} \le 0$.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 8, proof of Theorem 3.3, (3.5)–(3.6)

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting
import Definitions.Def_PDASNewton_NormCone_Setting

open Filter Topology Matrix

namespace PDASNewton.NormCone

theorem sum_decrease_3_6 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : RobinsonSR.Schur.IsPMatrix A)
    (hcone : ∀ S : Finset (Fin n), ∀ v : S → ℝ, 0 ≤ v → 0 ≤ ∑ i, ((PDASNewton.MMatrix.principal A S)⁻¹ *ᵥ v) i)
    (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, 1 ≤ k → ∀ S : Finset (Fin n), S = (PDASNewton.Local.activeSet c ψ (y k) (lam k))ᶜ →
      ∑ i, (y (k + 1) i - y k i) ≤
        -∑ i ∈ Sᶜ, (y k i - ψ i) +
          ∑ i : S, ((PDASNewton.MMatrix.principal A S)⁻¹ *ᵥ
            (PDASNewton.MMatrix.offDiag A S *ᵥ (fun j : (Sᶜ : Finset (Fin n)) => y k j - ψ j))) i := by sorry

end PDASNewton.NormCone
