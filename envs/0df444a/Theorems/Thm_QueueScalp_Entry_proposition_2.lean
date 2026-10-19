-- Prove2me | Theorems.Thm_QueueScalp_Entry_proposition_2
-- name    : QueueScalp.Entry.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:55.474376+00:00
-- url     : https://prove2.me/theorems/f5d11387-c4ea-488e-ab0c-f9396f6ff767
-- title:
--   Proposition 2 — optimal price and unimodality
-- statement:
--   For each demand volume $\Lambda>0$, the revenue-maximizing price of an entering single queue-scalper exists, is unique, and equals
--
--   $$P^*=\begin{cases}\dfrac{\Lambda(\sqrt\mu-\sqrt{\mu-\Lambda})}{\mu^2\sqrt{\mu-\Lambda}},&\Lambda\le\mu-1/V,\\[3pt]\dfrac{\Lambda V^2(\sqrt{\Lambda V+1}-1)}{(\Lambda V+1)^2},&\Lambda>\mu-1/V.\end{cases}$$
--
--   As a function of demand, $P^*$ increases strictly up to a peak and decreases strictly thereafter. The first clause identifies an actual optimizer of the paper's joint pricing and customer-equilibrium problem.
-- source:
--   Yang, Wang & Cui, A Model of Queue-Scalping, authors' manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3865), p. 11 (PDF 11), Proposition 2; proof, Online Appendix p. 2 (PDF 35), (A.1)–(A.3)

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model

namespace QueueScalp.Entry

theorem proposition_2 (P : Params) (hS : P.Standing) :
    (∀ Lam : ℝ, 0 < Lam → IsOptPrice P Lam (priceStar P Lam)) ∧
    (∀ Lam price : ℝ, 0 < Lam → IsOptPrice P Lam price →
      price = priceStar P Lam) ∧
    (∃ Lp : ℝ, 0 < Lp ∧
      StrictMonoOn (priceStar P) (Set.Ioc (0 : ℝ) Lp) ∧
      StrictAntiOn (priceStar P) (Set.Ici Lp)) := by sorry
end QueueScalp.Entry
