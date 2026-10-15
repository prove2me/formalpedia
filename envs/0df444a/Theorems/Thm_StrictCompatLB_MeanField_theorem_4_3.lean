-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_theorem_4_3
-- name    : StrictCompatLB.MeanField.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:51:30.716989+00:00
-- url     : https://prove2.me/theorems/6610a7a2-a983-4a0e-bd30-89a9f2bf1010
-- title:
--   Theorem 4.3 — process-level mean-field limit for Lipschitz policies on proportionally sparse graphs
-- statement:
--   Let $0<\lambda<1$, let $\{G_N\}_{N\ge1}$ be a proportionally sparse sequence of connected compatibility graphs, and let $\Pi$ be a Lipschitz continuous policy with assignment probability function $p^\Pi$. Suppose $q^*(0)\in\mathcal Y$ and $\|q(\Phi(G_N,0))-q^*(0)\|_1\to0$, and let $q^*$ be the solution, with values in $\mathcal Y$, of
--   $$\frac{dq^*_i(t)}{dt}=\lambda\,p^\Pi_{i-1}\big((q^*_j(t)-q^*_{j+1}(t))_{j\ge0}\big)-\big(q^*_i(t)-q^*_{i+1}(t)\big),\qquad i=1,2,\dots\qquad(4.2)$$
--   Then on every finite interval $[0,T]$ the occupancy process converges to $q^*$: for every $\varepsilon>0$,
--   $$P\Big(\sup_{t\in[0,T]}\|q(\Phi(G_N,t))-q^*(t)\|_1\ge\varepsilon\Big)\longrightarrow0\qquad(N\to\infty).$$
--
--   Under proportional sparsity, the system on a sparse compatibility graph has the same mean-field limit as the fully flexible system.
--
--   **Formalization Note** Weak convergence in the Skorohod $J_1$ topology to a deterministic continuous path is equivalent to convergence in probability of the supremum distance on $[0,T]$, which is what is stated. The solution of (4.2) is a hypothesis (any $\mathcal Y$-valued solution with the given initial value; by Remark 9 it is unique). The process is any realisation, for $N\ge1$, of the system routed by $\Pi$ (`piRoute`); $p^\Pi$ is required to be a probability vector vanishing at empty levels, so that this routing law is well defined. $\|\cdot\|_1$ is `l1dist` (coordinate $0$ equals $1$ on both sides).
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 16, Theorem 4.3, (4.2)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-- Theorem 4.3 (p. 16). On a proportionally sparse sequence of connected graphs, under a
Lipschitz continuous policy `Π` with assignment function `p`, if `q*(0) ∈ 𝒴` and the initial
occupancies converge to `q*(0)` in `ℓ₁`, then on every `[0, T]` the occupancy process
`q(Φ(G_N, ·))` converges in probability, uniformly in time and in `ℓ₁`, to the solution `q*`
of (4.2) with initial value `q*(0)` (equivalently: converges weakly in Skorohod `J₁` to the
continuous deterministic path `q*`). -/
theorem theorem_4_3 (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsparse : IsPropSparse M G)
    (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p) (hLip : IsLipschitzPolicy p)
    (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ) (hq₀ : InY q₀)
    (hinit : Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0))
    (s : ℝ → ℕ → ℝ) (hs : IsPiTrajectory lam p s) (hsY : ∀ t : ℝ, 0 ≤ t → InY (s t))
    (hs0 : s 0 = q₀)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ)
    (hproc : ∀ N, 1 ≤ N → IsLBProcess P lam M N (piRoute M G N p) (z₀ N) (Y N) (τ N)) :
    ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
        atTop (𝓝 0) := by sorry

end StrictCompatLB.MeanField
