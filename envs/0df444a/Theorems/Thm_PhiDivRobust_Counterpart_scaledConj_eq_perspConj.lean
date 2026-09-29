-- Prove2me | Theorems.Thm_PhiDivRobust_Counterpart_scaledConj_eq_perspConj
-- name    : PhiDivRobust.Counterpart.scaledConj_eq_perspConj
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:49:24.834984+00:00
-- url     : https://prove2.me/theorems/335f1058-669d-4fec-98af-c0fbca6ab391
-- title:
--   Proof of Theorem 1, closing identity: (λφ)*(s) = λφ*(s/λ) for λ ≥ 0
-- statement:
--   Let $\phi$ be a φ-divergence function with conjugate $\phi^*(s)=\sup_{t\ge0}\{st-\phi(t)\}$. For every $\lambda\ge0$ and $s\in\mathbb R$,
--
--   $$(\lambda\phi)^*(s) = \sup_{t\ge0}\{st-\lambda\phi(t)\} = \lambda\phi^*(s/\lambda),$$
--
--   where for $\lambda=0$ the right-hand side is defined as $0\phi^*(s/0) := (0\phi)^*(s)$, which equals $0$ if $s\le0$ and $+\infty$ if $s>0$.
--
--   This identity turns the separated dual function (15) into the left-hand side of the robust counterpart (13), including its convention at $\lambda = 0$.
--
--   **Formalization Note** Both sides are `EReal`-valued; $\lambda\phi(t)$ uses `EReal`'s $0\cdot(+\infty)=0$, and the $\lambda=0$ case of the right-hand side is the explicit case split of `perspConj`.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 347, proof of Theorem 1, closing paragraph (right column)

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction
import Definitions.Def_PhiDivRobust_Counterpart_conj
import Definitions.Def_PhiDivRobust_Counterpart_scaledConj
import Definitions.Def_PhiDivRobust_Counterpart_perspConj
open Matrix

namespace PhiDivRobust.Counterpart

/-- Ben-Tal et al. 2013, p. 347, proof of Theorem 1, closing paragraph: `(λφ)*(s) = λ φ*(s/λ)` for
`λ ≥ 0`, where `0 φ*(s/0) := (0φ)*(s)`, which equals `0` if `s ≤ 0` and `+∞` if `s > 0`. -/
theorem scaledConj_eq_perspConj (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (lam s : ℝ) (hlam : 0 ≤ lam) :
    scaledConj φ lam s = perspConj φ lam s := by sorry

end PhiDivRobust.Counterpart
