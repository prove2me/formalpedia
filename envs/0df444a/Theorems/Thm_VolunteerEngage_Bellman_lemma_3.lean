-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_lemma_3
-- name    : VolunteerEngage.Bellman.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:35.86996+00:00
-- url     : https://prove2.me/theorems/735c84a3-da04-420f-aa26-6db2b0114a55
-- title:
--   Lemma 3, Online Supplement p. 14 — ϕ is Lipschitz with constant max{|θ_k| : k = 0, …, L}
-- statement:
--   Fix parameters satisfying the standing assumptions, with breakpoints $\theta_0<\theta_1<\dots<\theta_L$ and conjugate $\phi(y)=\sup_{x\in[\theta_0,\theta_L]}\{yx-c(x)\}$. Let $C_L=\max\{|\theta_k|:k=0,1,\dots,L\}$. Then for all $y_1,y_2\in\mathbb R$
--
--   $$|\phi(y_1)-\phi(y_2)|\le C_L\,|y_1-y_2| .$$
--
--   The Lipschitz bound on $\phi$ is what makes the right-hand side of IVP($\beta$) Lipschitz in $v$, so that the initial value problem is well posed.
--
--   **Formalization Note.** The paper writes the index range as $k=0,\dots,K$; $K$ is the number of activities, called $L$ in the main text. The constant is the maximum of $|\theta_k|$ over $k\in\{0,\dots,L\}$, exactly as printed.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 14, Lemma 3

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Lemma 3 (Online Supplement p. 14): `ϕ` is Lipschitz continuous with Lipschitz constant
`C_L = max {|θ_k| : k = 0, 1, …, L}`. -/
theorem lemma_3 (M : Model) (hM : M.Standing) :
    ∀ y₁ y₂ : ℝ, |phi M y₁ - phi M y₂| ≤
      (Finset.range (M.L + 1)).sup' Finset.nonempty_range_add_one (fun k => |M.θ k|) *
        |y₁ - y₂| := by sorry

end VolunteerEngage.Bellman
