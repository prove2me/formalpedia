-- Prove2me | Theorems.Thm_QueueScalp_Entry_work_conservation
-- name    : QueueScalp.Entry.work_conservation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:00.243359+00:00
-- url     : https://prove2.me/theorems/6401820f-ca87-46d9-8b06-ecfab741e672
-- title:
--   Work conservation in proof of Lemma A.1
-- statement:
--   For throughput $0\le\lambda<\mu$ and purchase fraction $q\in[0,1]$, the weighted mean delay of buyers and nonbuyers equals the usual M/M/1 mean delay:
--
--   $$qW^I_1(\lambda,q)+(1-q)W^I_2(\lambda,q)=\frac1{\mu-\lambda}.$$
--
--   This identity connects the two customer delay classes to the equilibrium joining cutoff in Lemma A.1.
-- source:
--   Yang, Wang & Cui, A Model of Queue-Scalping, authors' manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3865), proof of Lemma A.1, Online Appendix p. 1 (PDF 34)

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model

namespace QueueScalp.Entry

theorem work_conservation (P : Params) (hS : P.Standing) (lam q : ℝ)
    (hlam : 0 ≤ lam) (hstable : lam < P.mu) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    q * W1 P.mu lam q + (1 - q) * W2 P.mu lam q = 1 / (P.mu - lam) := by sorry
end QueueScalp.Entry
