-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_theorem_24
-- name    : SharedVehicleApprox.Pricing.Supplement.theorem_24
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T18:38:07.580329+00:00
-- url     : https://prove2.me/theorems/7100ad6e-5998-421d-b0c2-b6a9bed5f2bd
-- title:
--   Theorem 24, p. 29 — bicriterion guarantee for multi-objective pricing (corrected: strongly connected support)
-- statement:
--   Let $\Phi_m$ and $\Psi_m$ be two objectives of the $m$-unit system with arrival rates $\varphi_{ij}\ge0$, both with reward curves concave on $[0,1]$, and let $c\ge0$. Let $\tilde q$ be an optimum of Algorithm 5, $\max\hat\Phi$ over balanced quantiles with $\hat\Psi\ge c$. Assume that the support graph of $\tilde q$ is strongly connected or that $\tilde q=0$, let $\tilde\pi$ be a stationary law under $\tilde q$, and put $\gamma=m/(m+n-1)$. Then:
--
--   1. for every state-dependent policy $q$ and every stationary law $\pi$ of it with $\Psi_m(q)\ge c$,
--   $$\Phi_m(\tilde q)\ge\gamma\,\Phi_m(q);$$
--   2. the requirement holds up to the same factor,
--   $$\Psi_m(\tilde q)\ge\gamma\,c.$$
--
--   Thus $\tilde q$ is a $(\gamma,\gamma)$ bicriterion approximation for maximizing one objective subject to a lower bound on another, as in Ramsey pricing.
--
--   Differences from the source:
--   - correction: no connectivity hypothesis → the support graph of q̃ is strongly connected or q̃ = 0; reason: false without it: n = 2, m = 2, φ_ij = 1 for all pairs, I_11 = I_22 = 1, I_12 = I_21 = 0 for both objectives, c = 0; all units at node 1 give Φ_m = 1 and one unit at each node gives 2, while 2/3 · 2 > 1. Excluded: nonzero q̃ with reducible routing
--   - encoding: Opt_m of the multi-objective problem → every state-dependent policy and stationary law with Ψ_m ≥ c; reason: the supremum over exactly the feasible set of the problem in §5.3; clause (i) claims nothing more when that set is empty
--   - encoding: the steady-state distribution, treated as unique (p. 7) → any probability vector on the finite state space that satisfies the balance equations; reason: the balance equations are the paper’s characterization of stationarity, and quantifying over all laws avoids assuming uniqueness
--   - generalization: per-ride rewards of prices, with I_ij(q) := I_ij(F_ij^{-1}(1 − q)) (pp. 6–8) → arbitrary real functions I_ij of the quantile, with R_ij(q) = q · I_ij(q); no F_ij; reason: every reward induced by value distributions is such a function, so the statement specializes to the paper’s
--   - encoding: the output of Algorithm 5 → any optimal solution of its relaxation; reason: the algorithm returns an optimum; the statement holds for each one and does not need existence
--   - generalization: the positive population and node counts of the vehicle-system setting → natural-number counts, including zero where the other hypotheses are satisfiable; reason: every positive source instance is retained. At m = 0 the only state is the zero-count state and objectives and flows are zero; at n = 0 and m > 0 no normalized stationary law exists. The availability maximum is used only with an explicit nonempty node type
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 29 (PDF 30), Theorem 24; Algorithm 5, p. 29 (PDF 30)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_MultiObjective

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Theorem 24, p. 29 (corrected: the support graph of `q̃` is strongly connected, unless
`q̃ = 0`): with `γ = m/(m+n−1)`, the output `q̃` of Algorithm 5 satisfies `Φ_m(q̃) ≥ γ Opt_m`, where
`Opt_m` is over state-dependent policies with `Ψ_m ≥ c`, and `Ψ_m(q̃) ≥ γ c`. -/
theorem theorem_24 {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (IΦ IΨ : Fin n → Fin n → ℝ → ℝ)
    (hΦ : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve IΦ i j))
    (hΨ : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve IΨ i j))
    (c : ℝ) (hc : 0 ≤ c)
    (qt : Fin n → Fin n → ℝ) (hopt : IsAlg5Optimal φ IΦ IΨ c qt)
    (hconn : SupportConnected φ qt ∨ qt = 0)
    (πt : (Fin n → ℕ) → ℝ) (hπt : IsStationary n m φ (toPolicy qt) πt) :
    (∀ (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ),
      IsPolicy n m q → IsStationary n m φ q π → c ≤ obj n m φ IΨ q π →
        (m : ℝ) / ((m : ℝ) + n - 1) * obj n m φ IΦ q π ≤ obj n m φ IΦ (toPolicy qt) πt) ∧
      (m : ℝ) / ((m : ℝ) + n - 1) * c ≤ obj n m φ IΨ (toPolicy qt) πt := by sorry

end SharedVehicleApprox.Pricing.Supplement
