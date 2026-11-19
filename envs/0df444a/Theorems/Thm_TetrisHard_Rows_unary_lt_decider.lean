-- Prove2me | Theorems.Thm_TetrisHard_Rows_unary_lt_decider
-- name    : TetrisHard.Rows.unary_lt_decider
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-18T20:08:06.414676+00:00
-- url     : https://prove2.me/theorems/897af3e3-0d2e-492a-a496-04a3bd6a30ae
-- title:
--   Unary comparison of a threshold with an answer is polynomial-time
-- statement:
--   There is a polynomial-time computable map $g$ on words over the tagged alphabet $\{\#\}\cup(\mathbb B\sqcup\mathbb B)$ such that for all natural numbers $a,v$,
--   $$g\bigl(\langle a\rangle\,\#\,\langle v\rangle\bigr)=[\,a<v\,],$$
--   where $\langle n\rangle=1^n0$ is the self-delimiting unary code, the left word is tagged with the first summand and the right word with the second.
--
--   This is the final comparison step of the gap decision procedure in Theorem 6.5.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, proof of Theorem 6.5 (p. 21), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_ThreePartition

namespace TetrisHard.Rows

theorem unary_lt_decider :
    ∃ g : List (Option (Bool ⊕ Bool)) → List Bool, CookPvsNP.PolyTimeComputable g ∧
      ∀ a v : ℕ, g ((unaryCode [a]).map (some ∘ Sum.inl) ++
        none :: (unaryCode [v]).map (some ∘ Sum.inr)) = [decide (a < v)] := by sorry

end TetrisHard.Rows
