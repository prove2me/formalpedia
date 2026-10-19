-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_corollary_6
-- name    : RandomLeadGBS.Diffusion.corollary_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:16.615303+00:00
-- url     : https://prove2.me/theorems/27438b01-bdd7-4581-9044-c273e09389d4
-- title:
--   Corollary 6, p. 20 — for every ϵ > 0 there is c > 0 with E[−c − Ŷ^r(∞)/√r]^+ ≤ ϵ for all large r
-- statement:
--   Under the standing assumptions, with centering $x_*\equiv 0$: for every $\epsilon>0$ there exist $c>0$ and $r_0$ such that for all $r\ge r_0$ and every stationary distribution of the artificial chain $\hat Y^r$, the expectation below is finite and
--   $$
--   \mathbb E\Big[-c - \frac{\hat Y^r(\infty)}{\sqrt r}\Big]^+ \le \epsilon . \tag{27}
--   $$
--   It controls the error term $\mathbb E[-f(r) - \gamma\hat Y^r(\infty)]^+$ in the proof of (36).
--
--   **Formalization Note** The page's "uniformly in $r$" is stated for all $r\ge r_0$: the corollary is derived from the limit statement Lemma 5 and is used only as $r\to\infty$. The series' summability is asserted. Centering $x_*\equiv 0$.
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, p. 20, Corollary 6, (27)

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion

theorem corollary_6 (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ r₀ : ℝ, ∀ r ≥ r₀, ∀ p : ℤ → ℝ, IsArtStationary P r p →
      Summable (fun j : ℤ => p j * max (-c - (j : ℝ) / Real.sqrt r) 0) ∧
      ∑' j : ℤ, p j * max (-c - (j : ℝ) / Real.sqrt r) 0 ≤ ε := by sorry

end RandomLeadGBS.Diffusion
