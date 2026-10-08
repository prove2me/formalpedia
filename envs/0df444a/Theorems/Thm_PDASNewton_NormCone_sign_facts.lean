-- Prove2me | Theorems.Thm_PDASNewton_NormCone_sign_facts
-- name    : PDASNewton.NormCone.sign_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:09.174149+00:00
-- url     : https://prove2.me/theorems/eb8ca7d6-5e20-41fe-aae1-d3f2ba4bd0e2
-- title:
--   Proof of Theorem 3.3, p. 8 — for k ≥ 1, λᵏ ≤ 0 on 𝓘_k and yᵏ ≥ ψ on 𝓐_k
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$, $f, \psi \in \mathbb{R}^n$ and $c > 0$, and let $(y^k, \lambda^k)_{k \ge 0}$ be a run of the primal-dual active set algorithm from arbitrary initial data. Write $\mathcal{A}_k = \{ i : \lambda^k_i + c(y^k_i - \psi_i) > 0\}$ and $\mathcal{I}_k$ for its complement. Then for every $k \ge 1$
--   $$\lambda^k_i \le 0 \quad (i \in \mathcal{I}_k), \qquad y^k_i \ge \psi_i \quad (i \in \mathcal{A}_k).$$
--
--   These are the two sign facts the proof of Theorem 3.3 imports from the proof of Theorem 3.2; they turn the identity (3.5) into the inequalities (3.6) and (3.7). They hold only from $k = 1$ on, after one step has made $\lambda^k$ and $y^k - \psi$ complementary.
--
--   **Formalization Note** No hypothesis on $A$ is needed. The assumption $c > 0$ is the paper's standing one ("for each $c > 0$") and is needed for the second fact: for $i \in \mathcal{A}_k$ with $\lambda^k_i = 0$ one has $c(y^k_i - \psi_i) > 0$.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 8, proof of Theorem 3.3 (facts established in the proof of Theorem 3.2, Appendix A, p. 20)

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting
import Definitions.Def_PDASNewton_NormCone_Setting

open Filter Topology Matrix

namespace PDASNewton.NormCone

theorem sign_facts {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, 1 ≤ k →
      (∀ i ∉ PDASNewton.Local.activeSet c ψ (y k) (lam k), lam k i ≤ 0) ∧
      (∀ i ∈ PDASNewton.Local.activeSet c ψ (y k) (lam k), ψ i ≤ y k i) := by sorry

end PDASNewton.NormCone
