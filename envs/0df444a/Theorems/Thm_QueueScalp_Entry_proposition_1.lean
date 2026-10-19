-- Prove2me | Theorems.Thm_QueueScalp_Entry_proposition_1
-- name    : QueueScalp.Entry.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:50.673011+00:00
-- url     : https://prove2.me/theorems/725fd070-2a2a-4894-bd9d-3e0fbb26c1c7
-- title:
--   Proposition 1 — avoid-the-crowd buying behavior
-- statement:
--   For a single queue-scalper under the head-queueing rule, let $0<\lambda<\mu$ be the throughput and let $q\in[0,1]$ be the fraction of joining customers who buy. The difference between nonbuyer and buyer expected delays is
--
--   $$D^I(q)=W^I_2(\lambda,q)-W^I_1(\lambda,q)=\frac{(\lambda/\mu)^2}{\mu-\lambda+\lambda q}.$$
--
--   The function $D^I$ is strictly decreasing on $[0,1]$: a higher buying fraction reduces an individual's delay gain from buying. This is the paper's avoid-the-crowd property.
--
--   **Formalization Note** The strict statement uses $\lambda>0$; at zero throughput the difference is constant. The paper's capacity, valuation, and cost assumptions are carried in `Standing`.
-- source:
--   Yang, Wang & Cui, A Model of Queue-Scalping, authors' manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3865), p. 10 (PDF 10), Proposition 1; proof, Online Appendix p. 1 (PDF 34)

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model

namespace QueueScalp.Entry

theorem proposition_1 (P : Params) (hS : P.Standing) (lam : ℝ)
    (hlam : 0 < lam) (hstable : lam < P.mu) :
    (∀ q ∈ Set.Icc (0 : ℝ) 1,
      D P.mu lam q = (lam / P.mu) ^ 2 / (P.mu - lam + lam * q)) ∧
      StrictAntiOn (D P.mu lam) (Set.Icc (0 : ℝ) 1) := by sorry
end QueueScalp.Entry
