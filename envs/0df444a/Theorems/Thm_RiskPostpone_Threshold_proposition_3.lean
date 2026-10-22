-- Prove2me | Theorems.Thm_RiskPostpone_Threshold_proposition_3
-- name    : RiskPostpone.Threshold.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:25.846051+00:00
-- url     : https://prove2.me/theorems/714933bd-82f5-4b86-b0f7-904db162a9a8
-- title:
--   Proposition 3 (concavity and threshold part; boundary corrected) — Π_r is concave and the responsive firm produces iff η > η*_r
-- statement:
--   In the random-yield model with its standing assumptions (in particular $p_0\ge c/\mu$), assume Assumption 2. Then
--
--   1. for every $\eta\in(0,1]$, the responsive objective $\Pi_r(q_r)$ is concave in $q_r\ge0$;
--   2. there is a risk-aversion threshold $\eta_r^*\in[0,1]$, with either $\eta_r^*=0$ or $p_0\,g(\eta_r^*)=c$, such that for every $\eta\in(0,1]$
--   $$
--   \text{the responsive firm produces at level }\eta\iff\eta>\eta_r^*.
--   $$
--   In particular, if $\eta<\eta_r^*$ it is optimal for the firm not to produce.
--
--   This is the counterpart of Proposition 2 under price postponement.
--
--   **Formalization Note** "Produces" means some $q\ge0$ gives strictly positive CVaR. The strict inequality $\eta>\eta_r^*$ corrects the boundary case of the paper's part (ii). The paper's "continuously differentiable" and the first-order equations of part (ii) are not stated. The characterization of $\eta_r^*$ is from the proof (p. ec8).
-- source:
--   Kouvelis, Xiao and Yang, Role of Risk Aversion in Price Postponement under Supply Random Yield, accepted manuscript MS-OPM-18-01273.R2 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3755), p. 13, Proposition 3 (concavity, part (i)); proof p. ec8 (PDF 41)

import Mathlib
import Definitions.Def_RiskPostpone_Threshold_Setting

open MeasureTheory Set

namespace RiskPostpone.Threshold

/-- Proposition 3, concavity and threshold part (p. 13; characterization from its proof,
p. ec8): under Assumption 2, (a) for every `η ∈ (0,1]`, `Π_r(q)` is concave in `q ≥ 0`;
(b) there is a risk-aversion threshold `η*_r ∈ [0,1]`, equal to `0` or a root of
`p0·g(η) = c`, such that for every `η ∈ (0,1]` the responsive firm produces (some `q ≥ 0` has
positive CVaR) iff `η > η*_r`. -/
theorem proposition_3 (M : Model) (hM : M.Standing) (hA2 : M.Assumption2) :
    (∀ η ∈ Ioc (0 : ℝ) 1, ConcaveOn ℝ (Ici 0) (fun q => M.PiR η q)) ∧
    ∃ ηr ∈ Icc (0 : ℝ) 1, (ηr = 0 ∨ M.p0 * M.tailMean ηr = M.c) ∧
      ∀ η ∈ Ioc (0 : ℝ) 1, (M.ProducesResponsive η ↔ ηr < η) := by sorry

end RiskPostpone.Threshold
