-- Prove2me | Theorems.Thm_QueueScalp_Entry_proposition_4
-- name    : QueueScalp.Entry.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:58.613324+00:00
-- url     : https://prove2.me/theorems/0d0acf00-648e-41b4-96d5-7f47da521ada
-- title:
--   Proposition 4 — entry occurs at intermediate demand
-- statement:
--   In the uniform-delay-cost single-scalper model with positive cost rate $k$, there are demand thresholds $\underline\Lambda\le\overline\Lambda$, fixed by capacity, valuation, and cost, such that for every $\Lambda>0$ an optimal revenue is attained and
--
--   $$N^*(\Lambda)=\begin{cases}1,&\underline\Lambda<\Lambda<\overline\Lambda,\\0,&\text{otherwise}.\end{cases}$$
--
--   Here $N^*$ compares the maximum entering profit $\Pi(\Lambda)-k$ with the zero profit from no entry. The interval may be empty when no demand covers the cost.
--
--   **Formalization Note** The paper's Proposition 4 relies on $k>0$ for the high-demand no-entry limit; this necessary hypothesis is explicit. At $\Pi=k$, entry is resolved as $N^*=0$, as in the proof's phrase “enters a queue (i.e., $\Pi>k$).” The expected delays of Lemma 1 are taken as given. Existence of an optimizer is in the conclusion for every positive demand, preventing a vacuous entry statement.
-- source:
--   Yang, Wang & Cui, A Model of Queue-Scalping, authors' manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3865), p. 12 (PDF 12), Proposition 4; proof, Online Appendix p. 3 (PDF 36)

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model

namespace QueueScalp.Entry

theorem proposition_4 (P : Params) (hS : P.Standing) (hk : 0 < P.k) :
    ∃ LamLo LamHi : ℝ, LamLo ≤ LamHi ∧
      ∀ Lam : ℝ, 0 < Lam →
        (∃ R, IsOptRevenue P Lam R) ∧
        ∀ R, IsOptRevenue P Lam R →
          ((LamLo < Lam ∧ Lam < LamHi) → entry P R = 1) ∧
          (¬ (LamLo < Lam ∧ Lam < LamHi) → entry P R = 0) := by sorry
end QueueScalp.Entry
