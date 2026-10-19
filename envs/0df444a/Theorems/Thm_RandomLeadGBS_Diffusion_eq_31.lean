-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_eq_31
-- name    : RandomLeadGBS.Diffusion.eq_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:13.398045+00:00
-- url     : https://prove2.me/theorems/d32bced2-c4b1-4ae6-9af9-e04e21cb7c23
-- title:
--   (31), p. 22 — E⌈T̂^r(∞)⌉ − E⌈T^r(∞)⌉ ≤ C for all large r
-- statement:
--   Under the standing assumptions, with centering $x_*\equiv 0$, there are $C>0$ and $r_0$ such that for every $r\ge r_0$, every stationary distribution of the GBS chain and every stationary distribution of the artificial chain, both expectations below are finite and
--   $$
--   \mathbb E\lceil\hat T^r(\infty)\rceil - \mathbb E\lceil T^r(\infty)\rceil \le C . \tag{31}
--   $$
--   The target gap between the artificial and the actual process is bounded. It feeds the comparison (47) in the proof of (36).
--
--   **Formalization Note** "For some finite $C>0$, uniformly in $r$" is stated for $r\ge r_0$: the page derives it from Lemma 4, which holds for all sufficiently large $r$. Summability of both series is asserted. Centering $x_*\equiv 0$.
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, p. 22, (31)

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion

theorem eq_31 (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, ∀ r ≥ r₀, ∀ (p : State → ℝ) (q : ℤ → ℝ),
      IsStationary P r p → IsArtStationary P r q →
      Summable (fun j : ℤ => q j * ((⌈truncTarget P r j⌉ : ℤ) : ℝ)) ∧
      Summable (fun s : State => p s * ((⌈truncTarget P r s.1⌉ : ℤ) : ℝ)) ∧
      ∑' j : ℤ, q j * ((⌈truncTarget P r j⌉ : ℤ) : ℝ) -
        ∑' s : State, p s * ((⌈truncTarget P r s.1⌉ : ℤ) : ℝ) ≤ C := by sorry

end RandomLeadGBS.Diffusion
