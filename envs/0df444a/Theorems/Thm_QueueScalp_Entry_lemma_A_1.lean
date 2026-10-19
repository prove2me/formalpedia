-- Prove2me | Theorems.Thm_QueueScalp_Entry_lemma_A_1
-- name    : QueueScalp.Entry.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:53.042013+00:00
-- url     : https://prove2.me/theorems/520f0778-f407-4d58-b40c-9f44b0ac9ba4
-- title:
--   Lemma A.1 — equilibrium joining cutoff
-- statement:
--   Suppose delay costs are uniform on $[0,1]$ and the one-scalper customer equilibrium has demand volume $\Lambda>0$. Its joining cutoff $c^S$ is independent of the scalper's price and satisfies
--
--   $$c^S=\begin{cases}1,&\Lambda\le\mu-1/V,\\ \mu V/(1+\Lambda V),&\Lambda>\mu-1/V.\end{cases}$$
--
--   The cutoff determines throughput $\lambda=\Lambda c^S$ and separates the all-join regime from the balking regime.
--
--   **Formalization Note** The paper also states this for pay-for-priority. This mission formalizes the queue-scalping half, using its customer-equilibrium predicate.
-- source:
--   Yang, Wang & Cui, A Model of Queue-Scalping, authors' manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3865), Online Appendix p. 1 (PDF 34), Lemma A.1

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model

namespace QueueScalp.Entry

theorem lemma_A_1 (P : Params) (hS : P.Standing) (Lam : ℝ)
    (hLam : 0 < Lam) (price lam q cS ct : ℝ)
    (heq : IsCustEq P Lam price lam q cS ct) :
    cS = cSOf P Lam := by sorry
end QueueScalp.Entry
