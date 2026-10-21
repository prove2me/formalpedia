-- Prove2me | Theorems.Thm_ReputationLies_Matching_proposition_3
-- name    : ReputationLies.Matching.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:58.773774+00:00
-- url     : https://prove2.me/theorems/7112ffd5-022d-474f-afac-5d656c1cce94
-- title:
--   Proposition 3 (i)–(ii), pp. 18–19 (PDF 20–21) — equilibrium hiring probability increases in reputation (top-heavy), decreases (bottom-heavy)
-- statement:
--   Throughout, the standing assumptions of §2 hold: $0 < s_L < s_H < 1$, $p \in (0,1)$, $g(r) > 0$ and $c(r) \in (0,r)$ for $r > 0$, $v(0) = 0$ and $v' > 0$, Assumption (A1) $L' > 0$, and the bias and outside-option laws are continuous with full support on $[0,1]$, $F$ being $C^1$ on $[0,1]$.
--
--   For a reputation $r > 0$ let $E_r[F(s_m)]$ be the ex-ante probability, in an equilibrium at $r$, that the firm hires the adviser's candidate (over the skill, the bias and the outside option, eq. (14)). Let $0 < r \le r'$ and take any equilibrium at $r$ and any equilibrium at $r'$.
--
--   1. (i) If the firm has a top-heavy market, then
--   $$E_r[F(s_m)] \le E_{r'}[F(s_m)],$$
--   with strict inequality whenever $r < r'$ and $L(r) < \bar B$.
--   2. (ii) If the firm has a bottom-heavy market, then
--   $$E_{r'}[F(s_m)] \le E_r[F(s_m)],$$
--   with strict inequality whenever $r < r'$ and $L(r) < \bar B$.
--
--   (iii) Consequently there is assortative matching: a firm with a top-heavy market is more likely to hire a candidate from an adviser with a stronger reputation, and a firm with a bottom-heavy market is more likely to hire a candidate from an adviser with a weaker reputation. Part (iii) is (i)–(ii) restated and is not a separate clause.
--
--   This is the paper's main result: the effect of an adviser's reputation on hiring depends on the shape of the firm's outside market, not only on its average.
--
--   **Formalization Note.** "Increasing" is read as weakly increasing on $(0,\infty)$ and strictly increasing from every $r$ with $L(r) < \bar B$. Where $L(r) \ge \bar B$ the adviser never lies (Proposition 1), so the hiring probability is constant on that set, and strict monotonicity on all of $(0,\infty)$ would be false. The statement quantifies over all equilibria at $r$ and $r'$, not over a particular constructed profile.
-- source:
--   Câmara, Jia & Raffiee, Reputation, competition, and lies in labor market recommendations, authors' manuscript of Sept. 26, 2022 (Management Science, doi:10.1287/mnsc.2022.4654), pp. 18–19 (PDF 20–21), Proposition 3; proof p. 40 (PDF 42)

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model

open Set

namespace ReputationLies.Matching

/-- Proposition 3 (i)–(ii), pp. 18–19: in equilibrium, the ex-ante probability `E[F(s_m)]` that the
firm hires the adviser's candidate is (i) in a top-heavy market, weakly increasing in the
reputation `r`, and strictly increasing from every `r` with `L(r) < B̄`; (ii) in a bottom-heavy
market, weakly decreasing, and strictly decreasing from every `r` with `L(r) < B̄`. -/
theorem proposition_3 (P : Primitives) (hP : P.Standing) :
    (P.TopHeavy →
      ∀ (r r' : ℝ) (σ σ' : Profile), 0 < r → r ≤ r' →
        IsEquilibrium P σ r → IsEquilibrium P σ' r' →
          exAnteHireProb P σ ≤ exAnteHireProb P σ' ∧
          (r < r' → P.L r < P.Bbar → exAnteHireProb P σ < exAnteHireProb P σ')) ∧
    (P.BottomHeavy →
      ∀ (r r' : ℝ) (σ σ' : Profile), 0 < r → r ≤ r' →
        IsEquilibrium P σ r → IsEquilibrium P σ' r' →
          exAnteHireProb P σ' ≤ exAnteHireProb P σ ∧
          (r < r' → P.L r < P.Bbar → exAnteHireProb P σ' < exAnteHireProb P σ)) := by sorry

end ReputationLies.Matching
