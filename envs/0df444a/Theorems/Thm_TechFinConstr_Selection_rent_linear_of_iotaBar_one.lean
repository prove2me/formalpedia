-- Prove2me | Theorems.Thm_TechFinConstr_Selection_rent_linear_of_iotaBar_one
-- name    : TechFinConstr.Selection.rent_linear_of_iotaBar_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:27.012644+00:00
-- url     : https://prove2.me/theorems/a4962327-f178-420e-8818-3c540ec5e0d9
-- title:
--   Proof of Proposition 6, p. 47 — if ῑ(p) = 1, Φᵢ(p) > 0 iff i = 1, and the agency rent is c/Φ*(p) on [0, π]
-- statement:
--   In Starmans' model, let $p\in\mathscr P$ with $\bar\iota(p)=1$, i.e. state $1$ is the only state with $p_i>q_i$. Then
--
--   1. $\Phi_i(p)>0$ if and only if $i=1$ (for $i\in\Omega$);
--   2. for every $c\in[0,\pi]$, problem (1) has an optimal contract, and every optimal contract $s$ has agency rent
--   $$\mathbb E_q[s]=\frac{c}{\Phi^*(p)} .$$
--
--   So an entrepreneur who improves only the left tail of the cash-flow distribution has a linear agency rent function with slope $1/\Phi^*(p)$. This is the first step of the proof of Proposition 6.
-- source:
--   Starmans, Technological Determinants of Financial Constraints, manuscript (February 4, 2022), p. 47, Appendix A.14 (proof of Proposition 6), first paragraph: "First note that Lemma 3 implies that if ῑ(p′) = 1 we have Φᵢ(p′) > 0 if and only if i = 1. In particular, by Proposition 2, the agency rent function for entrepreneur p′ is linear." and "The slope of the agency rent function for p′ is given by 1/Φ*(p′)."

import Mathlib
import Definitions.Def_TechFinConstr_Selection_Model

namespace TechFinConstr.Selection

theorem rent_linear_of_iotaBar_one {n : ℕ} (E : Economy n) (hE : E.Standing)
    (p : Fin (n + 1) → ℝ) (hp : InP E p) (h1 : (iotaBar E p).val = 1) :
    (∀ j : Fin (n + 1), 0 < Phi E p j ↔ j.val = 1) ∧
    ∀ c, 0 ≤ c → c ≤ E.piE →
      (∃ s, IsOptimalContract E p c s) ∧
      ∀ s, IsOptimalContract E p c s → expect E.q s = c / PhiStar E p := by sorry

end TechFinConstr.Selection
