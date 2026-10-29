-- Prove2me | Theorems.Thm_PutermanMDP_Sensitive_complementary_rank
-- name    : PutermanMDP.Sensitive.complementary_rank
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:26.612449+00:00
-- url     : https://prove2.me/theorems/0ef91d4f-6689-41f1-9ce2-c4cba719e70c
-- title:
--   Lemma 10.3.4 — complementary rank identity
-- statement:
--   Let $F,H$ be real $m\times m$ matrices. If $F+H$ has full rank and $FH=0$, then
--   $$\operatorname{rank}(F)+\operatorname{rank}(H)=m.$$
--   The identity connects the rank of a chain's limiting matrix with the rank of its deviation matrix. It does not assume symmetry or add the reverse product condition $HF=0$.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 517 (PDF 533), Lemma 10.3.4; https://doi.org/10.1002/9780470316887

import Mathlib

namespace PutermanMDP.Sensitive

theorem complementary_rank (m : ℕ) (F H : Matrix (Fin m) (Fin m) ℝ)
    (hfull : (F + H).rank = m) (hzero : F * H = 0) :
    F.rank + H.rank = m := by sorry

end PutermanMDP.Sensitive
