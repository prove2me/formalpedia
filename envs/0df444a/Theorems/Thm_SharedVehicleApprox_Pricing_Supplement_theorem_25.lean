-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_theorem_25
-- name    : SharedVehicleApprox.Pricing.Supplement.theorem_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:42:09.222576+00:00
-- url     : https://prove2.me/theorems/39375fc7-1758-4407-b6bd-98a4e381afbb
-- title:
--   Theorem 25 (companion theorem) — connected pricing approximates every conserved infinite-unit throughput
-- statement:
--   Let $n\ge1$, let $\varphi_{ij}\ge0$ have strongly connected support, and let $f_{ij}$ be any conserved flow with $0\le f_{ij}\le\varphi_{ij}$. For every $\varepsilon>0$ there are balanced quantiles $q'_{ij}\in[0,1]$ with strongly connected support such that
--
--   $$\mathrm{Obj}_\infty^T(q')\ge(1-\varepsilon)\sum_{i,j}f_{ij}.$$
--
--   Here throughput uses per-ride rewards one, and the infinite-unit objective is evaluated at the constant traffic vector one, or equivalently at any positive traffic solution. Every infinite-unit flow allowed by the source is a conserved demand-bounded flow, by Propositions 7 and 8. This formulation covers every allocation of units among components without choosing an invariant vector for a reducible routing matrix. It retains the paper's standing strong connectivity of the underlying demand graph. This is a companion theorem, independent of the published goal's proof.
--
--   Differences from the source:
--   - generalization: the infinite-unit flow f(q) of state-independent quantiles on k components → every nonnegative conserved matrix f bounded by φ; reason: Propositions 7 and 8 give these properties to every source flow, including every limit of finite stationary flows regardless of component allocation; the proof begins by replacing it with a balanced feasible flow. No source instance is excluded
--   - generalization: there exists a strongly connected q′ with the throughput bound → q′ is also balanced, and the bound holds for objInf at ρ = 1 and at every positive traffic solution; reason: the proof constructs balanced demand; its infinite-unit flow is φq′ by Lemma 11 and all positive traffic solutions are proportional. The explicit witness ρ = 1 prevents vacuity
--   - encoding: nodes [n] and throughput in the infinite-unit system → Fin n with n ≥ 1, and objInf φ (fun _ _ _ => 1) q′ ρ; reason: these are precisely the source throughput and Proposition 6 availability conventions
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 34 (PDF 35), Theorem 25

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Theorem 25, Appendix A, p. 34: any nonnegative conserved flow bounded by demand
can be approximated in throughput by a balanced quantile policy with connected support.
This includes every infinite-unit flow in the source, independently of the allocation of
units among its components (Propositions 7 and 8). The output has positive infinite-unit
flow on precisely its demand support, and its throughput is computed by `objInf`. -/
theorem theorem_25 {n : ℕ} [NeZero n]
    (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (hconn : SupportConnected φ (fun _ _ => 1))
    (f : Fin n → Fin n → ℝ) (hf : ∀ i j, 0 ≤ f i j ∧ f i j ≤ φ i j)
    (hbal : ∀ i, ∑ j, f i j = ∑ k, f k i)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q' : Fin n → Fin n → ℝ,
      IsRelaxFeasible φ q' ∧ SupportConnected φ q' ∧
      (1 - ε) * (∑ i, ∑ j, f i j) ≤ objInf φ (fun _ _ _ => 1) q' (fun _ => 1) ∧
      ∀ (ρ : Fin n → ℝ), (∀ i, 0 < ρ i) → IsTraffic φ q' ρ →
        (1 - ε) * (∑ i, ∑ j, f i j) ≤ objInf φ (fun _ _ _ => 1) q' ρ := by sorry

end SharedVehicleApprox.Pricing.Supplement
