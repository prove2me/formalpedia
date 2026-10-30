-- Prove2me | Theorems.Thm_SideConstrainedDTA_Existence_claim_6
-- name    : SideConstrainedDTA.Existence.claim_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:28.383135+00:00
-- url     : https://prove2.me/theorems/54b195c8-788a-471c-b432-93c361e3de22
-- title:
--   Claim 6, proof of Theorem 7.6, p. 40 — the weak limit h* of equilibria for penalties λ_n → ∞ is capacity-feasible, h* ∈ S
-- statement:
--   Work in the edge-capacity model of §7 with departure time choice, under the standing model and assumptions (A2), (A3), (A5) and (A9)–(A19). Let $(\lambda_n)$ be strictly positive numbers with $\lambda_n\to\infty$, and let $h^n\in\Lambda(Q)$ be, for each $n$, an unconstrained dynamic equilibrium (3) with respect to the penalized delay operator
--   $$\Psi^{\lambda_n}_p(h,t)=\Psi_p(h,t)+\lambda_n\sum_{e=(v_j,v_{j+1})\in p}\max\{0,f_e(h,\tau^j_p(h,t))-c_e(\tau^j_p(h,t))\}.$$
--   If $h^n$ converges weakly to $h^*\in\Lambda(Q)$, then $h^*$ is capacity-feasible:
--   $$f_e(h^*,\theta)\le c_e(\theta)\qquad\text{for all edges }e\text{ and }\theta\ge0,$$
--   that is, $h^*\in S$.
--
--   This is the first half of the proof that the penalty limit is a strong MNSDE.
--
--   **Formalization Note.** The context sentence of p. 40 (the sequences $\lambda_n$, $h^n$ and the weak limit $h^*$) is carried as hypotheses; the subsequence extraction is already done. Continuity of capacities (A22) is not assumed: the interval step of the proof needs only (A9), (A11)–(A13). Node indices are 0-based (`tau h p j t` is $\tau^{j+1}_p(h,t)$).
-- source:
--   Graf, Harks, Side-Constrained Dynamic Traffic Equilibria, arXiv:2211.03194v3, p. 40, proof of Theorem 7.6, Claim 6 (with the preceding paragraph)

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence

/-- Claim 6, proof of Theorem 7.6, p. 40: if `λ_n > 0`, `λ_n → ∞`, each `h^n` is a dynamic
equilibrium (3) w.r.t. `Ψ^{λ_n}`, and `h^n` converges weakly to `h* ∈ Λ(Q)`, then `h*` is
capacity-feasible, `h* ∈ S`. -/
theorem claim_6 {I W E : Type*} [Fintype I] [Fintype W] [Fintype E] [DecidableEq I]
    [DecidableEq W] [DecidableEq E] (N : Model I W E) (hN : N.Standing)
    (h2 : A2 N) (h3 : A3 N) (h5 : A5 N) (h9 : A9 N) (h10 : A10 N) (h11 : A11 N) (h12 : A12 N)
    (h13 : A13 N) (h14 : A14 N) (h15 : A15 N) (h16 : A16 N) (h17 : A17 N) (h18 : A18 N)
    (h19 : A19 N)
    (lam : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (hlam' : Tendsto lam atTop atTop)
    (hs : ℕ → W → ℝ → ℝ) (heq : ∀ n, IsDTCEq N (PsiPen N (lam n)) (hs n))
    (hstar : W → ℝ → ℝ) (hLam : Lam N hstar) (hweak : WeakTendsto N hs hstar) :
    capFeasible N hstar := by sorry

end SideConstrainedDTA.Existence
