-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_gordon_newell_reduction
-- name    : SharedVehicleApprox.Pricing.gordon_newell_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:14.105153+00:00
-- url     : https://prove2.me/theorems/dbdc0fc2-bc17-428e-8a9b-eeb5dd2afe59
-- title:
--   §2.3, p. 9 — a state-independent policy q yields a Gordon–Newell network with service rate Σ_j φ_ij q_ij and routing φ_ij q_ij/Σ_k φ_ik q_ik
-- statement:
--   Let $\varphi_{ij}\ge0$ be arrival rates and $q\in[0,1]^{n\times n}$ a state-independent quantile matrix with $\mu_i=\sum_j\varphi_{ij}q_{ij}>0$ at every node. Put $P_{ij}=\varphi_{ij}q_{ij}/\mu_i$. Then the $m$-unit system run under $q$ (rides from empty stations suppressed) is the Gordon–Newell (closed Jackson) network with single servers of rate $\mu_i$ and routing matrix $P$:
--
--   1. $P$ is a routing matrix: $P_{ij}\ge0$ and $\sum_jP_{ij}=1$;
--   2. for every $m$, a law $\pi$ is stationary for $q$ in the $m$-unit system (balance equation (1)) if and only if it is a steady state of the closed network with $m$ customers (flow-balance equations with rate $\mu_i\mathbf 1\{x_i>0\}$ at node $i$);
--   3. $r$ solves the traffic equations $\sum_jr_j\varphi_{ji}q_{ji}=r_i\sum_k\varphi_{ik}q_{ik}$ if and only if $\mu_ir_i=\sum_j\mu_jP_{ji}r_j$ for all $i$;
--   4. the support graph of $q$ is strongly connected if and only if $P$ is irreducible.
--
--   This is what lets the Gordon–Newell theorem (Theorem 2) be applied to state-independent pricing policies.
--
--   Differences from the source:
--   - encoding: "we obtain a Gordon-Newell network with service rate Σ_j φ_ij q_ij and routing probabilities φ_ij q_ij / Σ_k φ_ik q_ik" → P is a routing matrix, and the stationary laws and traffic solutions of q coincide with the steady states and traffic solutions of the closed network (µ, P); reason: this is what "is a Gordon–Newell network" means for the objects the paper uses (stationary laws, traffic intensities), in the vocabulary of the reused closed-network definitions
--   - encoding: service rate µ_i = Σ_j φ_ij q_ij (Definition 1, p. 8, requires µ_i > 0) → hypothesis 0 < Σ_j φ_ij q_ij for every i; reason: the routing probabilities φ_ij q_ij/µ_i are undefined at µ_i = 0, and Definition 1 requires µ_i > 0
--   - generalization: the reduction sentence of p. 9 → additionally: the support graph of q is strongly connected iff P is irreducible; reason: the extra clause links the paper's irreducibility assumption (p. 7, App. A) to the hypothesis of Theorem 2; it only adds to the reduction
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 9 (PDF 10), §2.3 ("Recall that for an m-unit system with state-independent policy p …"); Definition 1, p. 8 (PDF 9)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

open Finset QueueingFundamentals.Networks Filter Topology

namespace SharedVehicleApprox.Pricing

/-- §2.3, p. 9: a state-independent `q` run in the `m`-unit system is a Gordon–Newell network
with service rate `μ_i = ∑_j φ_ij q_ij` and routing probabilities `P_ij = φ_ij q_ij / μ_i`:
`P` is a routing matrix; the stationary laws of `toPolicy q` are exactly the steady states of
that closed network; the rate-form traffic equations are its traffic equations; and the support
graph of `q` is strongly connected iff `P` is irreducible. -/
theorem gordon_newell_reduction {n : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (q : Fin n → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ 1)
    (hmu : ∀ i, 0 < ∑ j, φ i j * q i j) :
    let mu : Fin n → ℝ := fun i => ∑ j, φ i j * q i j
    let P : Fin n → Fin n → ℝ := fun i j => φ i j * q i j / mu i
    IsRoutingMatrix P ∧
      (∀ (m : ℕ) (π : (Fin n → ℕ) → ℝ),
        IsStationary n m φ (toPolicy q) π ↔ IsClosedSteadyState mu P m π) ∧
      (∀ r : Fin n → ℝ, IsTraffic φ q r ↔ IsTrafficSolution mu P r) ∧
      (SupportConnected φ q ↔ IsIrreducible P) := by sorry

end SharedVehicleApprox.Pricing
