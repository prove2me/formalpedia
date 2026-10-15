-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_proposition_4_5
-- name    : StrictCompatLB.MeanField.proposition_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:51:23.85138+00:00
-- url     : https://prove2.me/theorems/f2badd14-bd3f-4404-b90e-3f6996367124
-- title:
--   Proposition 4.5 — on proportionally sparse graphs, few dispatchers are ε-bad on [0, T]
-- statement:
--   Let $0<\lambda<1$ and let $\{G_N\}_{N\ge1}$ be a proportionally sparse sequence of connected compatibility graphs. Let the system on $G_N$ use any routing laws, and suppose $q^*(0)\in\mathcal Y$ and $\|q(\Phi(G_N,0))-q^*(0)\|_1\to0$. Let $B^\varepsilon_N(t)$ be the number of $\varepsilon$-bad dispatchers in state $\Phi(G_N,t)$, i.e. of $w$ with $\sum_{i\ge0}|x_i-x^w_i|\ge\varepsilon$. Then for every $\varepsilon,\delta>0$ and $T\ge0$
--   $$P\Big(\sup_{t\in[0,T]}B^\varepsilon_N(t)\ge\delta M(N)\Big)\longrightarrow0\qquad(N\to\infty).$$
--
--   So, uniformly on finite time intervals, the local empirical queue length distribution seen by almost every dispatcher is close to the global one; this is the first ingredient of the process-level limit.
--
--   **Formalization Note** The routing laws are arbitrary (Remark 10: the proposition "does not depend on the task assignment policy or even on the dynamics in any way"), so the statement covers both Lipschitz policies $\Pi$ and JSQ(d). The supremum of the integer-valued $B^\varepsilon_N$ is written as "there is $t\in[0,T]$ with $B^\varepsilon_N(t)\ge\delta M(N)$". Connectivity is carried as in Definition 3.1.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 17, Proposition 4.5, (4.4); p. 16, Definition 4.4; pp. 42–44, App. F

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-- Proposition 4.5 (p. 17; proof App. F, pp. 42–44). On a proportionally sparse sequence of
connected graphs, for any routing laws (Remark 10: the result does not depend on the policy),
if the initial occupancies converge in `ℓ₁` to some `q*(0) ∈ 𝒴`, then for all `ε, δ > 0` and
`T ≥ 0`, `P(sup_{t ∈ [0,T]} B^ε_N(t) ≥ δ M(N)) → 0`. -/
theorem proposition_4_5 (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsparse : IsPropSparse M G)
    (route : (N : ℕ) → Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (hroute : ∀ N, 1 ≤ N → IsRoutingRule M G N (route N))
    (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ) (hq₀ : InY q₀)
    (hinit : Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ)
    (hproc : ∀ N, 1 ≤ N → IsLBProcess P lam M N (route N) (z₀ N) (Y N) (τ N)) :
    ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ T : ℝ, 0 ≤ T →
      Tendsto (fun N => P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
          δ * (M N : ℝ) ≤ (badCount M G N ε (statePath (Y N) (τ N) ω t) : ℝ)})
        atTop (𝓝 0) := by sorry

end StrictCompatLB.MeanField
