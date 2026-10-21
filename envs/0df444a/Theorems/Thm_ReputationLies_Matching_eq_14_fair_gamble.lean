-- Prove2me | Theorems.Thm_ReputationLies_Matching_eq_14_fair_gamble
-- name    : ReputationLies.Matching.eq_14_fair_gamble
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:06.136242+00:00
-- url     : https://prove2.me/theorems/394e377e-0081-4db6-880c-864e10ccc95e
-- title:
--   Proof of Proposition 3, eq. (14), p. 40 (PDF 42) — the message is a fair gamble on beliefs with mean ŝ; E[F(s_m)] formula
-- statement:
--   Throughout, the standing assumptions of §2 hold: $0 < s_L < s_H < 1$, $p \in (0,1)$, $g(r) > 0$ and $c(r) \in (0,r)$ for $r > 0$, $v(0) = 0$ and $v' > 0$, Assumption (A1) $L' > 0$, and the bias and outside-option laws are continuous with full support on $[0,1]$, $F$ being $C^1$ on $[0,1]$.
--
--   Fix $r > 0$ and an equilibrium at $r$, with beliefs $s_R$, $s_{NR}$. Then $\Pr(m = NR) = 1 - \Pr(m = R)$, the message is a fair gamble on the firm's beliefs,
--   $$\Pr(m = R)\,s_R + (1 - \Pr(m = R))\,s_{NR} = \hat s,$$
--   and the ex-ante probability that the focal candidate is hired is
--   $$E[F(s_m)] = \Pr(m = R)\,F(s_R) + (1 - \Pr(m = R))\,F(s_{NR}). \tag{14}$$
--
--   Reading $F$ as a utility function, the hiring probability is an expected utility over a fair gamble with mean $\hat s$; this is the representation used to prove Proposition 3.
-- source:
--   Câmara, Jia & Raffiee, Reputation, competition, and lies in labor market recommendations, authors' manuscript of Sept. 26, 2022 (Management Science, doi:10.1287/mnsc.2022.4654), p. 40 (PDF 42), proof of Proposition 3, eq. (14)

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model

open Set

namespace ReputationLies.Matching

/-- Proof of Proposition 3, eq. (14), p. 40: in an equilibrium at `r > 0`,
`Pr(m = NR) = 1 − Pr(m = R)`, the message is a fair gamble on the beliefs,
`Pr(m = R) sR + (1 − Pr(m = R)) sNR = ŝ`, and the ex-ante hiring probability is
`E[F(s_m)] = Pr(m = R) F(sR) + (1 − Pr(m = R)) F(sNR)`. -/
theorem eq_14_fair_gamble (P : Primitives) (hP : P.Standing) (r : ℝ) (hr : 0 < r)
    (σ : Profile) (hσ : IsEquilibrium P σ r) :
    msgProb P σ false = 1 - msgProb P σ true ∧
    msgProb P σ true * σ.sR + (1 - msgProb P σ true) * σ.sNR = P.shat ∧
    exAnteHireProb P σ =
      msgProb P σ true * P.F σ.sR + (1 - msgProb P σ true) * P.F σ.sNR := by sorry

end ReputationLies.Matching
