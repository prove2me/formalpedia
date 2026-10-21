-- Prove2me | Theorems.Thm_TechFinConstr_Selection_proposition_6
-- name    : TechFinConstr.Selection.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:28.073384+00:00
-- url     : https://prove2.me/theorems/a7a79ae5-376d-4caa-be58-f357941c9ed2
-- title:
--   Proposition 6, p. 22 — ῑ(p′) = 1 < ῑ(p″): rents cross once if Φ*(p′) < Φ*(p″); p′ is cheaper on (0, π] if Φ*(p′) > Φ*(p″)
-- statement:
--   In Starmans' model, consider two entrepreneurs $p',p''\in\mathscr P$ with $\bar\iota(p')=1$ and $\bar\iota(p'')>\bar\iota(p')$: the first improves only the left tail of the cash-flow distribution, the second a higher region. Entrepreneur $a$ has a *lower agency rent* than entrepreneur $b$ at disutility $c$ if $\mathbb E_q[s_a]<\mathbb E_q[s_b]$ for optimal contracts $s_a,s_b$ of problem (1) for $a$ and $b$. Then:
--
--   0. for every $c\in(0,\pi]$, both entrepreneurs have an optimal contract;
--   1. if $\Phi^*(p')<\Phi^*(p'')$, there is a threshold $\bar c\in(0,\pi)$ such that for every $c\in(0,\bar c)$ entrepreneur $p''$ has a lower agency rent than $p'$, and for every $c\in(\bar c,\pi]$ entrepreneur $p'$ has a lower agency rent than $p''$;
--   2. if $\Phi^*(p')>\Phi^*(p'')$, then for every $c\in(0,\pi]$ entrepreneur $p'$ has a lower agency rent than $p''$.
--
--   In formulas, case 1 reads
--   $$\exists\,\bar c\in(0,\pi):\quad \mathbb E_q[s''_c]<\mathbb E_q[s'_c]\ \ (0<c<\bar c),\qquad \mathbb E_q[s'_c]<\mathbb E_q[s''_c]\ \ (\bar c<c\le\pi),$$
--   for all optimal contracts $s'_c$ of $p'$ and $s''_c$ of $p''$ at $c$.
--
--   This is the paper's characterization of the investor's choice between entrepreneurs (the investor finances the one with the lower agency rent, hence the higher pledgeable income): the peak cumulative likelihood ratio $\Phi^*$ ranks entrepreneurs when effort is cheap, while at high disutility of effort the entrepreneur improving the left tail is cheaper.
--
--   **Formalization Note.** "Lower agency rent" is stated for every pair of optimal contracts; by footnote 7 (p. 11) all optimal contracts of an entrepreneur have the same agency rent, so this is the paper's comparison of $\mathbb E_q[s^*(p')]$ and $\mathbb E_q[s^*(p'')]$. Clause 0 (existence) is added so that the comparisons are not vacuous. Nothing is claimed at $c=\bar c$ or when $\Phi^*(p')=\Phi^*(p'')$, as on the page. The investor's capital $I$ does not enter.
-- source:
--   Starmans, Technological Determinants of Financial Constraints, manuscript (February 4, 2022), p. 22, Proposition 6 (proof p. 47, Appendix A.14)

import Mathlib
import Definitions.Def_TechFinConstr_Selection_Model

namespace TechFinConstr.Selection

theorem proposition_6 {n : ℕ} (E : Economy n) (hE : E.Standing)
    (p' p'' : Fin (n + 1) → ℝ) (hp' : InP E p') (hp'' : InP E p'')
    (h1 : (iotaBar E p').val = 1) (h2 : iotaBar E p' < iotaBar E p'') :
    (∀ c, 0 < c → c ≤ E.piE →
        (∃ s, IsOptimalContract E p' c s) ∧ ∃ s, IsOptimalContract E p'' c s) ∧
    (PhiStar E p' < PhiStar E p'' →
      ∃ cb, 0 < cb ∧ cb < E.piE ∧
        (∀ c, 0 < c → c < cb → ∀ s' s'', IsOptimalContract E p' c s' →
            IsOptimalContract E p'' c s'' → expect E.q s'' < expect E.q s') ∧
        (∀ c, cb < c → c ≤ E.piE → ∀ s' s'', IsOptimalContract E p' c s' →
            IsOptimalContract E p'' c s'' → expect E.q s' < expect E.q s'')) ∧
    (PhiStar E p'' < PhiStar E p' →
      ∀ c, 0 < c → c ≤ E.piE → ∀ s' s'', IsOptimalContract E p' c s' →
        IsOptimalContract E p'' c s'' → expect E.q s' < expect E.q s'') := by sorry

end TechFinConstr.Selection
