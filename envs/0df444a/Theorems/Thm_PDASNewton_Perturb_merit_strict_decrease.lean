-- Prove2me | Theorems.Thm_PDASNewton_Perturb_merit_strict_decrease
-- name    : PDASNewton.Perturb.merit_strict_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:58.61692+00:00
-- url     : https://prove2.me/theorems/ef55bc04-1c71-4943-9318-46cf894e9db3
-- title:
--   Proof of Theorem 3.4, pp. 9–10 — for small ‖K‖₁, Σᵢ(yᵏ⁺¹ᵢ − yᵏᵢ) < 0 unless yᵏ⁺¹ = yᵏ (k ≥ 1)
-- statement:
--   Let $M \in \mathbb{R}^{n\times n}$ be an M-matrix. There is $\varepsilon > 0$, depending only on $M$, such that for every $K \in \mathbb{R}^{n\times n}$ with $\|K\|_1 < \varepsilon$ ($\|\cdot\|_1$ the maximal absolute column sum) the following holds for $A = M + K$. For all $f, \psi \in \mathbb{R}^n$, every $c > 0$ and every run $(y^k,\lambda^k)_{k\ge0}$ of the primal-dual active set algorithm for (3.1), and every $k \ge 1$,
--   $$y^{k+1} \ne y^k \;\Longrightarrow\; \sum_{i=1}^n y^{k+1}_i < \sum_{i=1}^n y^k_i .$$
--   Thus $\mathcal{M}(y^k) = \sum_{i=1}^n y^k_i$ is a merit function for the algorithm.
--
--   Together with the finiteness of the possible active sets, this strict decrease is what yields convergence for arbitrary initial data in Theorem 3.4, "in the same manner as" for Theorem 3.3.
--
--   **Formalization Note** "$\|K\|_1$ can be chosen sufficiently small" is read as one $\varepsilon$ depending only on $M$ (and $n$), chosen before $f$, $\psi$, $c$ and the run; the page's smallness conditions involve only $M$ and $K$. The restriction $k \ge 1$ is the page's: the sign facts $\lambda^k \le 0$ on $\mathcal{I}_k$ and $y^k \ge \psi$ on $\mathcal{A}_k$ used in (3.8) hold from the first iterate on, not for the arbitrary initial data. $c > 0$ is the paper's standing assumption.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, pp. 9–10, proof of Theorem 3.4, (3.8) and the merit-function conclusion

import Mathlib
import Definitions.Def_PDASNewton_Perturb_Setting

open Filter Topology Matrix

namespace PDASNewton.Perturb

theorem merit_strict_decrease {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsMMatrix M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ K : Matrix (Fin n) (Fin n) ℝ, oneNorm K < ε →
      ∀ (f ψ : Fin n → ℝ) (c : ℝ), 0 < c →
        ∀ y lam : ℕ → Fin n → ℝ, PDASNewton.Local.IsRun (M + K) f ψ c y lam →
          ∀ k, 1 ≤ k → y (k + 1) ≠ y k → ∑ i, y (k + 1) i < ∑ i, y k i := by sorry

end PDASNewton.Perturb
