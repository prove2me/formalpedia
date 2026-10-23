-- Prove2me | Theorems.Thm_SideConstrainedDTA_Existence_claim_5
-- name    : SideConstrainedDTA.Existence.claim_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:51.320703+00:00
-- url     : https://prove2.me/theorems/82c6b3d6-eeed-4bfd-ac97-5dc91489becb
-- title:
--   Claim 5 (with DTC), proof of Theorem 7.6, p. 40 — a uniform M bounds min_p ess inf {Ψ^λ_p(h,t) : h_p(t) < B_p} for all λ ≥ 0 and h ∈ Λ(Q)
-- statement:
--   Work in the edge-capacity model of §7 with departure time choice and the penalized delays $\Psi^\lambda_p(h,t)=\Psi_p(h,t)+\lambda\xi_p(h,t)$, where $\xi_p(h,t)=\sum_{e=(v_j,v_{j+1})\in p}\max\{0,f_e(h,\tau^j_p(h,t))-c_e(\tau^j_p(h,t))\}$. Assume the standing model, (A2) (every commodity has a walk), (A10) (an outside option: for every $h\in\Lambda(Q)$ and commodity $i$ some walk $p\in\mathcal P_i$ is unsaturated with $h_p<B_p$ on a set of times of positive measure), (A18) (continuity and weak-uniform continuity of $\Psi$) and (A19) (a uniform bound on $\Psi$ over the feasible set $S$). Then there is $M\ge0$ such that for every $\lambda\ge0$, every commodity $i$ and every $h\in\Lambda(Q)$ there is a walk $p\in\mathcal P_i$ and a measurable set $J\subseteq[t_0,t_f]$ of positive measure with
--   $$h_p(t)<B_p\quad\text{and}\quad\Psi^\lambda_p(h,t)\le M\qquad\text{for all }t\in J.$$
--   In particular $\min_{p\in\mathcal P_i}\operatorname{ess\,inf}\{\Psi^\lambda_p(h,t)\mid t\in[t_0,t_f]:h_p(t)<B_p\}\le M$.
--
--   In the proof of Theorem 7.6 this bound caps the equilibrium cost levels $\nu_i$ uniformly in the penalty parameter $\lambda$.
--
--   **Formalization Note.** Only the case with departure time choice is posed. The essential-infimum form is replaced by the positive-measure set it follows from (avoiding `essInf` junk values on empty or unbounded sets). (A19) bounds $\Psi$ only on $S$, while $h$ ranges over $\Lambda(Q)$; (A18) is a hypothesis because the bound on all of $\Lambda(Q)$ comes from (A18) and weak sequential compactness of $\Lambda(Q)$. Node indices are 0-based (`tau h p j t` is $\tau^{j+1}_p(h,t)$).
-- source:
--   Graf, Harks, Side-Constrained Dynamic Traffic Equilibria, arXiv:2211.03194v3, p. 40, proof of Theorem 7.6, Claim 5 (case with DTC)

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence

/-- Claim 5 (with DTC), proof of Theorem 7.6, p. 40: there is `M ≥ 0` such that for all
`λ ≥ 0`, commodities `i` and `h ∈ Λ(Q)` some walk `p ∈ P_i` has a set of times of positive
measure in `[t0, tf]` on which `h_p < B_p` and `Ψ^λ_p(h, ·) ≤ M`. -/
theorem claim_5 {I W E : Type*} [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W]
    (N : Model I W E) (hN : N.Standing) (h2 : A2 N) (h10 : A10 N) (h18 : A18 N)
    (h19 : A19 N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ lam : ℝ, 0 ≤ lam → ∀ i h, Lam N h → ∃ p, N.com p = i ∧
      ∃ J ⊆ Icc N.t0 N.tf, MeasurableSet J ∧ 0 < volume J ∧
        ∀ t ∈ J, h p t < N.B p ∧ PsiPen N lam h p t ≤ M := by sorry

end SideConstrainedDTA.Existence
