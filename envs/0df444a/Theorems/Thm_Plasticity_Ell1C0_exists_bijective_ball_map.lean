-- Prove2me | Theorems.Thm_Plasticity_Ell1C0_exists_bijective_ball_map
-- name    : Plasticity.Ell1C0.exists_bijective_ball_map
-- status  : Proved
-- author  : @scanstone
-- created : 2026-11-18T19:25:09.991625+00:00
-- url     : https://prove2.me/theorems/71371bb4-0e90-4752-89c5-ceebbb3b8914
-- title:
--   A nonexpansive bijection from the ball of $\ell_1(\Gamma)$ onto the ball of $c_0(\Gamma)$, $|\Gamma|=\mathfrak c$, with norm-one preimages of points tending to $0$
-- statement:
--   Let $\Gamma$ be a set of cardinality continuum.
--   There is a nonexpansive bijection $F\colon B_{\ell_1(\Gamma)}\to B_{c_0(\Gamma)}$ with $F(0)=0$ and points $u_m$ of norm one ($m\in\mathbb N$) with $\|F(u_m)\|=1/(m+2)$; in particular $F^{-1}$ is discontinuous at $0$.
-- source:
--   Proof draft 'Three constructions of nonplastic Banach unit balls' (ChatGPT Pro, OpenAI, 18 November 2026), Construction A

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.SetTheory.Cardinal.Continuum

namespace Plasticity
theorem Ell1C0.exists_bijective_ball_map (Γ : Type*)
    (hΓ : Cardinal.mk Γ = Cardinal.continuum) :
    ∃ F : Metric.closedBall (0 : lp (fun _ : Γ => ℝ) 1) 1 → Metric.closedBall (0 : c0 Γ) 1,
      LipschitzWith 1 F ∧ Function.Bijective F ∧
      F ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = ⟨0, Metric.mem_closedBall_self zero_le_one⟩ ∧
      ∃ u : ℕ → Metric.closedBall (0 : lp (fun _ : Γ => ℝ) 1) 1,
        ∀ m, ‖(u m : lp (fun _ : Γ => ℝ) 1)‖ = 1 ∧ ‖(F (u m) : c0 Γ)‖ = 1 / ((m : ℝ) + 2) := by sorry
end Plasticity
