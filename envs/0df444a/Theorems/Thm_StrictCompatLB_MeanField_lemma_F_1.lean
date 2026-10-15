-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_lemma_F_1
-- name    : StrictCompatLB.MeanField.lemma_F_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:51:54.756874+00:00
-- url     : https://prove2.me/theorems/7b8d112f-78fe-45dd-b554-bf49bbd882a1
-- title:
--   Lemma F.1 — the tail occupancy stays small on [0, T]
-- statement:
--   Let $0<\lambda<1$, let $G_N$ be any compatibility graphs and let the system on $G_N$ use any routing laws. Suppose the starting states satisfy $\|q(\Phi(G_N,0))-q^*(0)\|_1\to0$ as $N\to\infty$ for some $q^*(0)\in\mathcal Y$. Then for each $\varepsilon>0$, $\delta>0$ and $T>0$ there exist $i_0\ge1$ and $N_1\ge1$ such that
--   $$P\Big(\sup_{t\in[0,T]}q_{i_0}(\Phi(G_N,t))\ge\varepsilon\Big)<\delta\qquad\text{for all }N\ge N_1 .$$
--
--   The lemma controls the mass at high queue lengths uniformly on a finite time interval, the first step in showing that local and global empirical distributions are close for almost all dispatchers.
--
--   **Formalization Note** The process $\Phi(G_N,\cdot)$ is any realisation, for $N\ge1$, of the uniformised chain with the given routing laws (`IsLBProcess`); the routing laws are arbitrary, as the paper notes that the lemma uses neither a graph condition nor a Lipschitz property. The event $\{\sup_{t\in[0,T]}q_{i_0}\ge\varepsilon\}$ is written as $\{\exists t\in[0,T]:q_{i_0}(\Phi(G_N,t))\ge\varepsilon\}$; the two coincide because a path has finitely many jumps on $[0,T]$ almost surely, so the supremum is attained. $i_0$ and $N_1$ may depend on all the data fixed before them.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 42, Lemma F.1, (F.1)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-- Lemma F.1 (p. 42). For any routing laws (no condition on the graphs, no Lipschitz property),
if the initial occupancies converge in `ℓ₁` to some `q*(0) ∈ 𝒴`, then for every `ε, δ, T > 0` there
are `i₀ ≥ 1` and `N₁ ≥ 1` with `P(sup_{t ∈ [0,T]} q_{i₀}(Φ(G_N, t)) ≥ ε) < δ` for all `N ≥ N₁`. -/
theorem lemma_F_1 (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (route : (N : ℕ) → Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (hroute : ∀ N, 1 ≤ N → IsRoutingRule M G N (route N))
    (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ) (hq₀ : InY q₀)
    (hinit : Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ)
    (hproc : ∀ N, 1 ≤ N → IsLBProcess P lam M N (route N) (z₀ N) (Y N) (τ N)) :
    ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ T : ℝ, 0 < T →
      ∃ i₀ : ℕ, 1 ≤ i₀ ∧ ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N ≥ N₁,
        P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, ε ≤ occPath (Y N) (τ N) ω t i₀} < ENNReal.ofReal δ := by sorry

end StrictCompatLB.MeanField
