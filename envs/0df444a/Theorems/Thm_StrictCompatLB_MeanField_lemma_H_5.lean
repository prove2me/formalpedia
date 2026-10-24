-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_lemma_H_5
-- name    : StrictCompatLB.MeanField.lemma_H_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:52:07.156456+00:00
-- url     : https://prove2.me/theorems/499d6d9d-427b-43a6-a903-afdc6ff6f868
-- title:
--   Lemma H.5 — Foster's drift condition ΔV_1 ≤ −1 + 2·𝟙{z ∈ C_Γ} with Γ = 3(1+λ)/(1−λ)·N
-- statement:
--   Let $0<\lambda<1$, $d\ge1$, and let $\{G_N\}_{N\ge1}$ be a sequence of connected graphs satisfying the subcriticality condition. There is $N_0\ge1$ such that for all $N\ge N_0$, under the JSQ(d) policy, the function $V_1(z)=\sum_{i\ge1}\sum_{j\ge i}Q_j(z)$ satisfies
--   $$\Delta V_1(z)\le-1+2\,\mathbb 1\{z\in C\}\qquad\text{for all }z\in\mathcal S_N,$$
--   where $C=C_\Gamma$ with $\Gamma=3\,\frac{1+\lambda}{1-\lambda}\,N$.
--
--   With Lemma H.4 this verifies the Foster–Lyapunov condition, giving positive Harris recurrence of the uniformised chain for all large $N$.
--
--   **Formalization Note** $\Delta V_1$ is the expected one-step increase for the uniformised chain. Connectivity is the standing assumption of §2.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 49, Lemma H.5, (H.14)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-- Lemma H.5 (p. 49). For a sequence of connected graphs satisfying the subcriticality condition,
there is `N₀ ≥ 1` such that for all `N ≥ N₀`, under JSQ(d), `V_1` satisfies (H.14):
`ΔV_1(z) ≤ −1 + 2·𝟙{z ∈ C}` for all states `z`, with `C = C_Γ`, `Γ = 3 (1+λ)/(1−λ) N`. -/
theorem lemma_H_5 (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsub : IsSubcritical d M G) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ z : Fin N → ℕ,
      oneStepDrift (jsqdKernel lam d M G N) (lyap 1) z ≤
        -1 + 2 * (CGamma N (3 * ((1 + lam) / (1 - lam)) * (N : ℝ))).indicator
          (fun _ => (1 : ℝ)) z := by sorry

end StrictCompatLB.MeanField
