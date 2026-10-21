-- Prove2me | Theorems.Thm_ReputationLies_Matching_step_4_bayes_belief
-- name    : ReputationLies.Matching.step_4_bayes_belief
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:54.188303+00:00
-- url     : https://prove2.me/theorems/181f818c-ceb6-4829-89e5-de334d45c6e3
-- title:
--   Proof of Proposition 1, Step 4, eq. (11), p. 38 (PDF 40) — Bayes belief after a recommendation is sR(b∗), strictly increasing and continuous
-- statement:
--   Throughout, the standing assumptions of §2 hold: $0 < s_L < s_H < 1$, $p \in (0,1)$, $g(r) > 0$ and $c(r) \in (0,r)$ for $r > 0$, $v(0) = 0$ and $v' > 0$, Assumption (A1) $L' > 0$, and the bias and outside-option laws are continuous with full support on $[0,1]$, $F$ being $C^1$ on $[0,1]$.
--
--   Suppose the adviser uses a bias threshold $b^* \in (0,1]$: on $[0,1]$, an adviser with a high-skilled candidate always recommends, and an adviser with a low-skilled candidate recommends exactly when $b > b^*$ (the strategies are measurable). Then Bayes' rule gives the firm's belief after a recommendation as
--   $$s_R(b^*) = \frac{p\,s_H + (1-p)(1-Z(b^*))\,s_L}{p + (1-p)(1-Z(b^*))}. \tag{11}$$
--   Moreover, $b^* \mapsto s_R(b^*)$ is strictly increasing and continuous on $[0,1]$, with $s_R(0) = \hat s$ (an adviser who always lies leaves the firm at its prior) and $s_R(1) = s_H$ (an adviser who never lies is fully trusted).
--
--   This identifies the equilibrium belief with the threshold and is used in Proposition 1 and in the proof of Proposition 3.
--
--   **Formalization Note.** Monotonicity and continuity are stated on the closed interval $[0,1]$, which contains the page's $(0,1)$; the boundary values are those stated on p. 13.
-- source:
--   Câmara, Jia & Raffiee, Reputation, competition, and lies in labor market recommendations, authors' manuscript of Sept. 26, 2022 (Management Science, doi:10.1287/mnsc.2022.4654), p. 38 (PDF 40), proof of Proposition 1, Step 4, eq. (11); boundary values sR(0) = ŝ, sR(1) = sH from p. 13 (PDF 15)

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model

open Set

namespace ReputationLies.Matching

/-- Proof of Proposition 1, Step 4, eq. (11), p. 38: if the adviser uses the bias threshold
`b∗ ∈ (0, 1]` (high-skilled types always recommend, low-skilled types recommend iff `b > b∗`),
the Bayes belief after a recommendation is `sR(b∗)`; `sR` is strictly increasing and
continuous on `[0, 1]`, with `sR(0) = ŝ` and `sR(1) = sH` (p. 13). -/
theorem step_4_bayes_belief (P : Primitives) (hP : P.Standing) :
    (∀ (σ : Profile) (bstar : ℝ), bstar ∈ Ioc (0 : ℝ) 1 →
      Measurable (fun b => σ.σA b true) → Measurable (fun b => σ.σA b false) →
      (∀ b ∈ Icc (0 : ℝ) 1, σ.σA b true = true) →
      (∀ b ∈ Icc (0 : ℝ) 1, (σ.σA b false = true ↔ bstar < b)) →
      bayesBelief P σ true = P.sRof bstar) ∧
    StrictMonoOn P.sRof (Icc 0 1) ∧ ContinuousOn P.sRof (Icc 0 1) ∧
    P.sRof 0 = P.shat ∧ P.sRof 1 = P.sH := by sorry

end ReputationLies.Matching
