-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_lemma_H_2
-- name    : StrictCompatLB.MeanField.lemma_H_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:51:49.808233+00:00
-- url     : https://prove2.me/theorems/93c66920-9a08-462a-821e-051bbac38ec9
-- title:
--   Lemma H.2 — drift of the Lyapunov functions V_k under JSQ(d) on subcritical graphs
-- statement:
--   Let $0<\lambda<1$, $d\ge1$, and let $\{G_N\}_{N\ge1}$ be a sequence of connected graphs satisfying the subcriticality condition. For each $\varepsilon>0$ there is $N_0\ge1$ such that under the JSQ(d) policy, for all $N\ge N_0$, all $k\ge1$ and all states $z\in\mathcal S_N$,
--   $$\Delta V_k(z)\le\frac1{\lambda+1}\Big((1+\varepsilon)\lambda\,q_{k-1}(z)-\big(1-(1+\varepsilon)\lambda\big)\sum_{i=k}^\infty q_i(z)\Big),$$
--   where $V_k(z)=\sum_{i\ge k}\sum_{j\ge i}Q_j(z)$ and $\Delta V_k(z)=\mathbb E[V_k(\Phi(G_N,t_1))-V_k(\Phi(G_N,t_0))\mid\Phi(G_N,t_0)=z]$ is the expected increase over one step of the uniformised chain.
--
--   The bound says that when the tail of the occupancy is heavy compared with $q_{k-1}$, the Lyapunov function decreases; it drives both the stability and the moment bounds of the steady states.
--
--   **Formalization Note** $N_0$ depends only on $\varepsilon$ (and the fixed data), not on $k$ or $z$. Connectivity is the standing assumption of §2; it guarantees that the JSQ(d) routing law is a probability vector at every dispatcher.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 47, Lemma H.2, (H.4); p. 46, (H.1); p. 47, (H.3)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-- Lemma H.2 (p. 47). For a sequence of connected graphs satisfying the subcriticality condition,
for each `ε > 0` there is `N₀ ≥ 1` such that under JSQ(d), for all `N ≥ N₀`, all `k ≥ 1` and all
states `z`, the one-step drift of the uniformised chain satisfies (H.4):
`ΔV_k(z) ≤ (1/(λ+1)) ((1+ε) λ q_{k−1}(z) − (1 − (1+ε)λ) ∑_{i ≥ k} q_i(z))`. -/
theorem lemma_H_2 (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsub : IsSubcritical d M G) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ k : ℕ, 1 ≤ k → ∀ z : Fin N → ℕ,
      oneStepDrift (jsqdKernel lam d M G N) (lyap k) z ≤
        1 / (lam + 1) * ((1 + ε) * lam * occ z (k - 1) - (1 - (1 + ε) * lam) * tailSum k z) := by sorry

end StrictCompatLB.MeanField
