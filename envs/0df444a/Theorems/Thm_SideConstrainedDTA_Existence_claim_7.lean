-- Prove2me | Theorems.Thm_SideConstrainedDTA_Existence_claim_7
-- name    : SideConstrainedDTA.Existence.claim_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:23.054099+00:00
-- url     : https://prove2.me/theorems/999aa317-cd9d-4c6d-b2b5-68dc134a2639
-- title:
--   Claim 7, proof of Theorem 7.6, p. 41 — with continuous capacities (A22) added, the feasible penalty limit h* is a strong MNSDE
-- statement:
--   Work in the edge-capacity model of §7 with departure time choice, under the standing model, assumptions (A2), (A3), (A5), (A9)–(A19), and continuity of every capacity function $c_e$ on $\mathbb R_{\ge0}$ (A22). Let $(\lambda_n)$ be strictly positive numbers with $\lambda_n\to\infty$, and let $h^n\in\Lambda(Q)$ be an unconstrained dynamic equilibrium (3) with respect to the penalized delay operator $\Psi^{\lambda_n}$ (as in Claim 6). Suppose $h^n$ converges weakly to $h^*\in\Lambda(Q)$ and $h^*$ is capacity-feasible, $h^*\in S$ (Claim 6). Then $h^*$ is a side-constrained dynamic equilibrium with respect to $S$ and the admissible $\gamma$-deviations (26):
--   $$\Psi_p(h^*,t)\le\Psi_q(h^*,t+\Delta)\qquad\text{for all }p,\ t\in[t_0,t_f],\ (q,\Delta)\in U_p(h^*,t).$$
--   So $h^*$ is a strong MNSDE.
--
--   Together with Claim 6 this completes the proof of Theorem 7.6.
--
--   **Formalization Note.** (A22) is added: the paper's Theorem 7.6 assumes only (A11)–(A12) on the capacities, but the third step of this proof (transferring strict slack $f_e<c_e$ from $h^*$ to $h^n$) and the claim that $\Psi^\lambda$ satisfies (A4) need continuity of $c_e$. (A17) is posed for all $h\in\Lambda(Q)$ because this proof applies it to the infeasible $h^n$. Node indices are 0-based (`tau h q j t` is $\tau^{j+1}_q(h,t)$).
-- source:
--   Graf, Harks, Side-Constrained Dynamic Traffic Equilibria, arXiv:2211.03194v3, pp. 41–42, proof of Theorem 7.6, Claim 7 (context p. 40); (A22) from p. 45

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence

/-- Claim 7, proof of Theorem 7.6, p. 41, with continuous capacities (A22) added: in the setting
of Claim 6, the feasible weak limit `h*` is an SCDE w.r.t. the admissible γ-deviations (26),
i.e. a strong MNSDE. -/
theorem claim_7 {I W E : Type*} [Fintype I] [Fintype W] [Fintype E] [DecidableEq I]
    [DecidableEq W] [DecidableEq E] (N : Model I W E) (hN : N.Standing)
    (h2 : A2 N) (h3 : A3 N) (h5 : A5 N) (h9 : A9 N) (h10 : A10 N) (h11 : A11 N) (h12 : A12 N)
    (h13 : A13 N) (h14 : A14 N) (h15 : A15 N) (h16 : A16 N) (h17 : A17 N) (h18 : A18 N)
    (h19 : A19 N) (h22 : A22 N)
    (lam : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (hlam' : Tendsto lam atTop atTop)
    (hs : ℕ → W → ℝ → ℝ) (heq : ∀ n, IsDTCEq N (PsiPen N (lam n)) (hs n))
    (hstar : W → ℝ → ℝ) (hLam : Lam N hstar) (hweak : WeakTendsto N hs hstar)
    (hfeas : capFeasible N hstar) :
    IsSCDE N N.Psi (capFeasible N) (devMNS N) hstar := by sorry

end SideConstrainedDTA.Existence
