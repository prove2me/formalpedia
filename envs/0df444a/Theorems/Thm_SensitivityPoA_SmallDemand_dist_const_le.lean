-- Prove2me | Theorems.Thm_SensitivityPoA_SmallDemand_dist_const_le
-- name    : SensitivityPoA.SmallDemand.dist_const_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:08.206979+00:00
-- url     : https://prove2.me/theorems/8e90958e-0cd3-4d17-bd37-e05c1e83ade8
-- title:
--   p. 43, first display — ‖Γ′ − Λ_{T(d)}(Γ)‖ = max_{a,x∈[0,1]} |τ_a(T(d)x) − τ_a(0)| = max_a |τ_a(T(d)) − τ_a(0)| ≤ M_τ·T(d)
-- statement:
--   Let $\tau = (\tau_a)_{a \in A}$ be cost functions (continuous, non-decreasing and non-negative on $[0,\infty)$), each Lipschitz on $[0, b]$ with constant $M_\tau$. Let $d \ge 0$ be a demand vector with $0 < T(d) \le b$, and put $\Gamma = (\tau, d)$. Let $\sigma_a(x) \equiv \tau_a(0)$ be the constant costs and $\Gamma' = (\sigma, d/T(d))$ the auxiliary game of total demand $1$. Then
--   $$\|\Gamma' - \Lambda_{T(d)}(\Gamma)\| = \max_{a \in A,\ x \in [0,1]} |\tau_a(T(d)\cdot x) - \tau_a(0)| = \max_{a \in A} |\tau_a(T(d)) - \tau_a(0)| \le M_\tau \cdot T(d).$$
--
--   It says that, after normalization to total demand $1$, a game of small total demand is close to the constant-cost game $\Gamma'$, at distance linear in $T(d)$.
--
--   **Formalization Note** Each $\max$ is a real supremum of the image of the indicated set (the first) or Mathlib's sup norm on $\mathbb R^A$ (the second); both are $0$ when there are no arcs. The paper writes $\sigma_a(x)$ in the middle term; here it is written $\tau_a(0)$. Strict positivity of $\tau$ is not needed and not assumed.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 43, §5.2, first display

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_SmallDemand_Setting

namespace SensitivityPoA.SmallDemand

open KellyStochasticNetworks

/-- p. 43, first display: for `Γ = (τ, d)`, the auxiliary game `Γ' = (σ, d/T(d))` with constant
costs `σ_a ≡ τ_a(0)` and the normalized game `Λ_{T(d)}(Γ)` satisfy
`‖Γ' − Λ_{T(d)}(Γ)‖ = max_{a, x ∈ [0,1]} |τ_a(T(d)·x) − σ_a(x)| = max_a |τ_a(T(d)) − τ_a(0)| ≤ M_τ·T(d)`
when `T(d) ≤ b`. -/
theorem dist_const_le {N : Network} (τ : Fin N.J → ℝ → ℝ) (hτ : ∀ j, IsCostFn (τ j))
    (b Mτ : ℝ) (hLip : ∀ j, LipOnIcc (τ j) b Mτ)
    (d : Fin N.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) (hT : 0 < totalDemand d) (hTb : totalDemand d ≤ b) :
    gameDist (⟨fun j _ => τ j 0, fun k => d k / totalDemand d⟩ : Game N)
        (demandNormalize (totalDemand d) (⟨τ, d⟩ : Game N)) =
      sSup ((fun p : Fin N.J × ℝ => |τ p.1 (totalDemand d * p.2) - τ p.1 0|) ''
        (Set.univ ×ˢ Set.Icc 0 1)) ∧
    sSup ((fun p : Fin N.J × ℝ => |τ p.1 (totalDemand d * p.2) - τ p.1 0|) ''
        (Set.univ ×ˢ Set.Icc 0 1)) = ‖fun j => τ j (totalDemand d) - τ j 0‖ ∧
    ‖fun j => τ j (totalDemand d) - τ j 0‖ ≤ Mτ * totalDemand d := by sorry

end SensitivityPoA.SmallDemand
