-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_propagator_spec
-- name    : TDHamSim.QueryOptimal.propagator_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:17:14.830422+00:00
-- url     : https://prove2.me/theorems/d6162feb-2913-4ace-b8fa-d3afe52e3a3d
-- title:
--   §3 — existence and unitarity of the propagator
-- statement:
--   Let $H$ be an $n$-qubit Hermitian Hamiltonian on $[0,T]$, with $\alpha>0$, $\beta\ge0$, $T>0$, $\|H(t)\|\le\alpha$ and $\|H(t)-H(s)\|\le\beta|t-s|$. The selected propagator exists with the initial-value characterization
--
--   $$iU_H'(t)=H(t)U_H(t),\qquad U_H(0)=I,$$
--
--   and $U_H(t)$ is unitary for every $t\in[0,T]$. This makes explicit the evolution object used throughout the paper. The ODE is understood one-sided at the two endpoints, and its continuation outside the interval is irrelevant.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
--   - encoding: the propagator denoted U_H in §3 → a choice from the ODE solutions, with existence and unitarity asserted as a separate target; reason: this exposes the existence obligation without assuming a resource certificate or a closed-form commuting evolution
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), §3 — existence and unitarity of the propagator, p.11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_Model

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- §3, p.11: the propagator exists and is unitary; the choice definition satisfies its ODE. -/
theorem propagator_spec {n : ℕ} (H : ℝ → Mat (Bits n)) (α β T : ℝ)
    (hα : 0 < α) (hβ : 0 ≤ β) (hT : 0 < T) (hH : IsHamiltonian H α β T) :
    IsPropagator H (propagator H T) T ∧
      ∀ t ∈ Set.Icc 0 T, IsUnitary (propagator H T t) := by sorry

end TDHamSim.QueryOptimal
