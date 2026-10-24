-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_theorem_4_8_ii
-- name    : StrictCompatLB.MeanField.theorem_4_8_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:52:03.106996+00:00
-- url     : https://prove2.me/theorems/440796db-b132-4118-b7ab-7770fba721e4
-- title:
--   Theorem 4.8(ii) — the stationary occupancies are tight in ℓ^ω_1 for geometric weights with ratio r ∈ (1, 2/(1+λ))
-- statement:
--   Let $0<\lambda<1$, $d\ge1$, and let $\{G_N\}_{N\ge1}$ be a sequence of connected graphs satisfying the subcriticality condition. Fix $r\in(1,2/(1+\lambda))$ and a positive sequence $\omega=(\omega_1,\omega_2,\dots)$ with
--   $$\omega_{i_0+i}=\omega_{i_0}r^i\qquad\text{for }i\ge1\qquad(4.17)$$
--   for some $i_0\in\mathbb N$. Then there is $N_0\ge1$ such that the JSQ(d) system on $G_N$ has a steady state $\Phi(G_N,\infty)$ for every $N\ge N_0$, and the sequence $\{q(\Phi(G_N,\infty))\}_{N\ge N_0}$ is tight when $\mathcal Y$ is endowed with the $\ell^\omega_1$-topology.
--
--   Tightness in a weighted space whose weights grow geometrically is what lets the limit of the steady states be identified through the global stability of the mean-field ODE.
--
--   **Formalization Note** The steady states exist only for large $N$ (Theorem 4.8(i)), so the sequence starts at $N_0$, and the existence of stationary distributions for $N\ge N_0$ is part of the conclusion (so $N_0$ cannot be chosen where none exist). Tightness is `IsTightWeighted`, for any choice of stationary distributions.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 20, Theorem 4.8(ii), (4.17)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-- Theorem 4.8(ii) (p. 20). For a sequence of connected graphs satisfying the subcriticality
condition, fix `r ∈ (1, 2/(1+λ))` and positive weights `ω` with `ω_{i₀+i} = ω_{i₀} r^i` for
`i ≥ 1` (4.17). Then there is `N₀ ≥ 1` such that the JSQ(d) chain on `G_N` has a stationary
distribution for every `N ≥ N₀`, and for any choice of stationary distributions `π N`
(`N ≥ N₀`) the laws of `q(Φ(G_N, ∞))` are tight in `ℓ^ω_1`. -/
theorem theorem_4_8_ii (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsub : IsSubcritical d M G)
    (r : ℝ) (hr1 : 1 < r) (hr2 : r < 2 / (1 + lam))
    (ω : ℕ → ℝ) (hω : ∀ i, 1 ≤ i → 0 < ω i) (i₀ : ℕ)
    (h417 : ∀ i : ℕ, 1 ≤ i → ω (i₀ + i) = ω i₀ * r ^ i) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      (∀ N ≥ N₀, ∃ π : (Fin N → ℕ) → ℝ, IsStationary (jsqdKernel lam d M G N) π) ∧
      ∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
        (∀ N ≥ N₀, IsStationary (jsqdKernel lam d M G N) (π N)) → IsTightWeighted ω N₀ π := by sorry

end StrictCompatLB.MeanField
