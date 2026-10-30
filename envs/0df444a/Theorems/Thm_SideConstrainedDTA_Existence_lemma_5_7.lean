-- Prove2me | Theorems.Thm_SideConstrainedDTA_Existence_lemma_5_7
-- name    : SideConstrainedDTA.Existence.lemma_5_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:20.80466+00:00
-- url     : https://prove2.me/theorems/919330cc-d37a-4da1-9a9b-8f3e519232aa
-- title:
--   Lemma 5.7, p. 23 — if every nonempty U_p(h,t) has an alternative of delay < M, SCDE w.r.t. Ψ and w.r.t. the truncation Ψ|^M coincide
-- statement:
--   Let $S$ be a constraint set, $A_p$ correspondences of admissible $\gamma$-deviations with admissible alternatives $U_p(h,t)$ as in (18), $\Phi$ an effective walk delay operator, and $M\in\mathbb R$. For $t\in[t_0,t_f]$ let $\Phi|^M_p(h,t)=\min\{\Phi_p(h,t),M\}$ be the truncated operator. Assume that for all $h\in S$, $t\in[t_0,t_f]$ and walks $p$ with $U_p(h,t)\ne\emptyset$ there is $(q,\Delta)\in U_p(h,t)$ with
--   $$\Phi_q(h,t+\Delta)<M .$$
--   Then any walk inflow $h^*$ is an SCDE (w.r.t. $S$ and $A$) for $\Phi$ if and only if it is an SCDE for $\Phi|^M$.
--
--   The lemma lets one replace an unbounded delay operator by a bounded one without changing the equilibria, as long as a cheap alternative is always available.
--
--   **Formalization Note.** The truncated operator is defined at every time, not only on $[t_0,t_f]$; the SCDE condition evaluates it at $t+\Delta$.
-- source:
--   Graf, Harks, Side-Constrained Dynamic Traffic Equilibria, arXiv:2211.03194v3, p. 23, Lemma 5.7 and Definition 5.6

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence

/-- Lemma 5.7, p. 23: if for all `h ∈ S`, `t ∈ [t0, tf]` and `p` with `U_p(h, t) ≠ ∅` some
`(q, Δ) ∈ U_p(h, t)` has `Φ_q(h, t + Δ) < M`, then `h*` is an SCDE w.r.t. `Φ` iff it is an SCDE
w.r.t. the truncation `Φ|^M`. -/
theorem lemma_5_7 {I W E : Type*} [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W]
    (N : Model I W E) (hN : N.Basic) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ)
    (S : (W → ℝ → ℝ) → Prop) (A : Corr W) (M : ℝ)
    (hM : ∀ h, S h → ∀ t ∈ Icc N.t0 N.tf, ∀ p, (admDev N A h p t).Nonempty →
      ∃ x ∈ admDev N A h p t, Φ h x.1 (t + x.2) < M) (hs : W → ℝ → ℝ) :
    IsSCDE N Φ S A hs ↔ IsSCDE N (PsiTrunc Φ M) S A hs := by sorry

end SideConstrainedDTA.Existence
