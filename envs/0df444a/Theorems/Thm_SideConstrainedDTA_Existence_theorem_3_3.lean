-- Prove2me | Theorems.Thm_SideConstrainedDTA_Existence_theorem_3_3
-- name    : SideConstrainedDTA.Existence.theorem_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:29.997656+00:00
-- url     : https://prove2.me/theorems/8734bcb9-a09c-432c-b79b-a3ccc7cdc029
-- title:
--   Theorem 3.3 (fixed-flow-volume case), p. 12 — under (A1), h* ∈ Λ(Q) is a DTC equilibrium (3) iff it solves VI(Ψ, Q, [t0, tf])
-- statement:
--   Consider the dynamic traffic model with departure time choice: walks $p$ grouped into commodities $\mathcal P_i$, horizon $[t_0,t_f]$, flow volumes $Q_i$, inflow bounds $B_p$, and the feasible set $\Lambda(Q)$. Let $\Phi$ be an effective walk delay operator such that, for every $h\in\Lambda(Q)$ and walk $p$, the function $\Phi_p(h,\cdot)$ is measurable and bounded on $[t_0,t_f]$ (assumption (A1)). Then $h^*\in\Lambda(Q)$ is a dynamic equilibrium with fixed flow volumes and departure time choice, i.e. there are $\nu_i\in\mathbb R$ with
--   $$h^*_p(t)>0\Rightarrow\Phi_p(h^*,t)\le\nu_i,\qquad h^*_p(t)<B_p\Rightarrow\Phi_p(h^*,t)\ge\nu_i$$
--   for almost all $t\in[t_0,t_f]$ and all $p\in\mathcal P_i$, if and only if $h^*$ solves the variational inequality
--   $$\langle\Phi(h^*),h-h^*\rangle=\sum_{p}\int_{t_0}^{t_f}\Phi_p(h^*,t)\big(h_p(t)-h^*_p(t)\big)\,dt\ \ge0\qquad\text{for all }h\in\Lambda(Q).$$
--
--   The characterization turns equilibrium existence into a variational-inequality existence question, which Theorem 3.4 answers.
--
--   **Formalization Note.** Only the fixed-flow-volume half (inflows in $\Lambda(Q)$) is posed; the fixed-inflow-rate half on $\Lambda(r)$ is not. The delay operator is a generic real-valued $\Phi$ (the paper states it for $\Psi$; the proof of Theorem 7.6 applies it to the penalized and truncated operator). Its measurability on $[t_0,t_f]$ is stated as a hypothesis (the paper's $\Psi$ maps into measurable functions, p. 10). Inflows are functions; see the definitions file for the conventions.
-- source:
--   Graf, Harks, Side-Constrained Dynamic Traffic Equilibria, arXiv:2211.03194v3, p. 12, Theorem 3.3 (proof in Appendix D, pp. 58–60)

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence

/-- Theorem 3.3, fixed-flow-volume case, p. 12: under (A1), for a delay operator `Φ` with
measurable values, `h* ∈ Λ(Q)` is a dynamic equilibrium with fixed flow volumes and departure
time choice (3) iff it solves `VI(Φ, Q, [t0, tf])`. -/
theorem theorem_3_3 {I W E : Type*} [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W]
    (N : Model I W E) (hN : N.Basic) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ)
    (hΦ : ∀ h, Lam N h → ∀ p, AEStronglyMeasurable (Φ h p) (volume.restrict (Icc N.t0 N.tf)))
    (h1 : A1 N Φ) (hs : W → ℝ → ℝ) (hhs : Lam N hs) :
    IsDTCEq N Φ hs ↔
      ∀ h, Lam N h → 0 ≤ ∑ p, ∫ t in Icc N.t0 N.tf, Φ hs p t * (h p t - hs p t) := by sorry

end SideConstrainedDTA.Existence
