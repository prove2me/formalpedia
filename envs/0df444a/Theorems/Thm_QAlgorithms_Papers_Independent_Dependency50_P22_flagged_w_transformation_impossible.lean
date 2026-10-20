-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P22_flagged_w_transformation_impossible
-- name    : QAlgorithms.Papers.Independent.Dependency50.P22.flagged_w_transformation_impossible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:26:07.070103+00:00
-- url     : https://prove2.me/theorems/53e75ab8-e09d-4073-9ccb-89b864b80421
-- title:
--   The flagged W-to-omega transformation is impossible by LOCC
-- statement:
--   Let Alice, Bob and Charlie share $|W\rangle=(|100\rangle+|010\rangle+|001\rangle)/\sqrt3$. In the ordered basis $00,01,10,11$, define
--   $$
--   \omega=\begin{pmatrix}0&0&0&0\\0&1/3&4/9&0\\0&4/9&2/3&0\\0&0&0&0\end{pmatrix}.
--   $$
--   There is no LOCC instrument with two distinct classical outcomes whose subnormalized outputs on this input are
--   $$
--   \tfrac12\omega^{AC}\otimes|0\rangle\langle0|^B,
--   \qquad
--   \tfrac12|0\rangle\langle0|^A\otimes\omega^{BC}.
--   $$
--   LOCC here includes linked infinite-round protocols without an additional entangled resource. Both probabilities are exactly $1/2$. The retained outcome flag is part of the transformation task.
-- source:
--   Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask), arXiv:1210.4583v2, PDF p. 14, §4.3, Eq.(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P22

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P22

open QAlgorithms.Papers.Independent.Information100.P27 (Config)

/-- PDF p.14, §4.3: no tripartite LOCC instrument realizes the flagged W-to-omega
transformation, with both branch probabilities exactly 1/2. -/
theorem flagged_w_transformation_impossible :
    ¬ ∃ J : Fin 2 → Superop (QConfig 3) (QConfig 3),
      InLOCC (fun _ : Fin 3 => 2) J ∧
      ∀ o, J o (pureDensity wKet) = (1 / 2 : ℂ) • omegaFlag o := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P22

end
