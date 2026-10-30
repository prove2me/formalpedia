-- Prove2me | Theorems.Thm_SideConstrainedDTA_Existence_theorem_3_5
-- name    : SideConstrainedDTA.Existence.theorem_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:28.634997+00:00
-- url     : https://prove2.me/theorems/db4fb0d9-a989-4aa5-94f8-541c23351b1d
-- title:
--   Theorem 3.5 (with departure time choice), p. 12 — under (A1)–(A4) a dynamic equilibrium with fixed flow volumes exists
-- statement:
--   In the dynamic traffic model with departure time choice, let $\Phi$ be an effective walk delay operator with measurable values $\Phi_p(h,\cdot)$ on $[t_0,t_f]$ for $h\in\Lambda(Q)$, and assume
--
--   1. (A1) for every $h\in\Lambda(Q)$ and walk $p$, $\Phi_p(h,\cdot)$ is bounded on $[t_0,t_f]$;
--   2. (A2) every commodity has at least one walk;
--   3. (A3) $\Lambda(Q)$ is non-empty;
--   4. (A4) for every walk $p$, the map $\Lambda(Q)\to L^2([t_0,t_f])$, $h\mapsto\Phi_p(h,\cdot)$, is sequentially weak-strong continuous.
--
--   Then there is a dynamic equilibrium with fixed flow volumes and departure time choice: some $h^*\in\Lambda(Q)$ and numbers $\nu_i$ such that, for almost all $t\in[t_0,t_f]$ and all $p\in\mathcal P_i$,
--   $$h^*_p(t)>0\Rightarrow\Phi_p(h^*,t)\le\nu_i,\qquad h^*_p(t)<B_p\Rightarrow\Phi_p(h^*,t)\ge\nu_i.$$
--
--   The proof of the paper's main existence theorem applies this result to the penalized, truncated delay operators $\Psi^\lambda|^{M+1}$.
--
--   **Formalization Note.** Only the half with departure time choice is posed. (A4) is stated as $\|\Phi_p(h^n,\cdot)-\Phi_p(h,\cdot)\|_{L^2([t_0,t_f])}\to0$ whenever $h^n\in\Lambda(Q)$ converges weakly to $h\in\Lambda(Q)$. Walk finiteness in (A2) is the finiteness of the walk type. Measurability of $\Phi_p(h,\cdot)$ is a hypothesis (the paper's delay operators map into measurable functions, p. 10).
-- source:
--   Graf, Harks, Side-Constrained Dynamic Traffic Equilibria, arXiv:2211.03194v3, p. 12, Theorem 3.5 and (A1)–(A4) (proof in Appendix D, pp. 60–61)

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence

/-- Theorem 3.5, with departure time choice, p. 12: under (A1)–(A4), for a delay operator `Φ`
with measurable values, a dynamic equilibrium with fixed flow volumes and departure time
choice (3) exists. -/
theorem theorem_3_5 {I W E : Type*} [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W]
    (N : Model I W E) (hN : N.Basic) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ)
    (hΦ : ∀ h, Lam N h → ∀ p, AEStronglyMeasurable (Φ h p) (volume.restrict (Icc N.t0 N.tf)))
    (h1 : A1 N Φ) (h2 : A2 N) (h3 : A3 N) (h4 : A4 N Φ) :
    ∃ h, IsDTCEq N Φ h := by sorry

end SideConstrainedDTA.Existence
