-- Prove2me | Theorems.Thm_StabTestMem_card_stochOrth_rank_le
-- name    : StabTestMem.card_stochOrth_rank_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:10:08.193445+00:00
-- url     : https://prove2.me/theorems/a1dcb788-0b22-4ce3-9850-a7244696c255
-- title:
--   Lemma 5.7 — at most $2^{rt}$ elements of $\mathcal O_t$ with $\mathrm{rank}(I+O)=r$
-- statement:
--   For all $t,r\ge0$, the number of matrices $O\in\mathcal O_t$ (that is, $O\in\mathbb F_2^{t\times t}$ with $OO^\top=O^\top O=I$) such that $\operatorname{rank}_{\mathbb F_2}(I+O)=r$ is at most $2^{rt}$.
--
--   Combined with $\operatorname{Tr}R(O)=2^{n(t-\operatorname{rank}(I+O))}$ this controls the non-identity part of $\sigma_P$ (Theorem 5.5).
--
--   Differences from the source: none.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 5.7, p. 40

import Definitions.Def_StabTestMem_IsStochOrth

namespace StabTestMem

open Classical in
/-- **Lemma 5.7: counting `O_t` by `rank(I + O)`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 5.7, p. 40: "The number of O ∈ O_t
such that rank(I + O) = r is no more than 2^{rt}."

For all `t, r`, at most `2^{rt}` matrices `O ∈ O_t` (`t × t` over `F₂`, `OOᵀ = OᵀO = I`) have
`rank(I + O) = r` (rank over `F₂`). -/
theorem card_stochOrth_rank_le (t r : ℕ) :
    (Finset.univ.filter fun O : Matrix (Fin t) (Fin t) (ZMod 2) =>
      IsStochOrth O ∧ (1 + O).rank = r).card ≤ 2 ^ (r * t) := by sorry

end StabTestMem
