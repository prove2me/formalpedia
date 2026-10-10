-- Prove2me | Theorems.Thm_SONATA_Push_phi_bounds
-- name    : SONATA.Push.phi_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:16:21.859959+00:00
-- url     : https://prove2.me/theorems/19e3c513-c02c-49f5-971d-e5c531bfbb24
-- title:
--   φ bounds, p. 29 — φ_lb ≤ φ_i^ν ≤ φ_ub for every agent and every iteration
-- statement:
--   In the standing setting (Assumptions A, B′, C, E, the constants (15), a solution $x^\star$), suppose $m\ge2$. For every run of Algorithm 3 with step size $\alpha\in(0,1]$, the push-sum weights satisfy
--   $$\phi_{lb}\le\phi_i^\nu\le\phi_{ub},\qquad\text{for all }i\in[m],\ \nu=0,1,\dots,$$
--   where $\phi_{lb}=c_\ell^{2(m-1)B}$ and $\phi_{ub}=m-c_\ell^{2(m-1)B}$.
--
--   The weights depend only on the matrices $C^\nu$. The bounds keep the normalizations $1/\phi_i^{\nu+1}$ of Algorithm 3 under control and enter Propositions 4.1 and 4.3 through $\phi_{ub}$ and $\phi_{lb}$.
--
--   **Formalization Note** The paper quotes these bounds from its reference [35, Prop. 1]. The hypothesis $m\ge2$ is added: for $m=1$ the printed $\phi_{ub}=1-c_\ell^0=0$, while $\phi^\nu\equiv1$.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 29, display after (79) (quoted from [35, Prop. 1]), with (78)

import Mathlib
import Definitions.Def_SONATA_Push_Network

namespace SONATA.Push

/-- The bounds on `φ_i^ν` (display after (79), p. 29, cited from [35, Prop. 1]):
`φ_lb ≤ φ_i^ν ≤ φ_ub` for all `i` and `ν`, with `φ_lb = c_ℓ^{2(m−1)B}`, `φ_ub = m − c_ℓ^{2(m−1)B}` (78).
Stated for `m ≥ 2`: at `m = 1` the printed `φ_ub = 0` while `φ ≡ 1`. -/
theorem phi_bounds
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (hm : 2 ≤ m)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x y xh : ℕ → Fin m → SONATA.Undir.E d) (φ : ℕ → Fin m → ℝ) (hrun : IsRun K f G ft C α x y xh φ) :
    ∀ ν : ℕ, ∀ i : Fin m, phiLb m B cl ≤ φ ν i ∧ φ ν i ≤ phiUb m B cl := by sorry

end SONATA.Push
