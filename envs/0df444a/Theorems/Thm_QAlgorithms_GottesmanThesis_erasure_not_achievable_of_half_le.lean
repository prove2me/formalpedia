-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanThesis_erasure_not_achievable_of_half_le
-- name    : QAlgorithms.GottesmanThesis.erasure_not_achievable_of_half_le
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T14:19:52.722471+00:00
-- url     : https://prove2.me/theorems/1158651f-514c-413a-a6da-764335cab4ad
-- title:
--   The quantum erasure channel with erasure probability $p \ge 1/2$ has no positive achievable rate
-- statement:
--   Let $1/2 \le p \le 1$ and $R>0$. Then $R$ is not an achievable rate,
--
--   $$\neg\,\mathrm{IsAchievableQRate}\big(n \mapsto \mathcal{E}_{n,p},\ R\big),$$
--
--    (in the entanglement-fidelity sense of `IsAchievableQRate`) for the $n$-qubit quantum erasure channel with erasure probability $p$.
--
--   Role: the zero-capacity half of the erasure-channel capacity formula $Q = \max(0, 1-2p)$; the parent combines it with achievability of $1-2p$ for $p<1/2$ and the matching converse.
-- source:
--   D. Gottesman, Stabilizer Codes and Quantum Error Correction (PhD thesis, Caltech 1997), arXiv:quant-ph/9705052, Section 7.5, p. 90 (no-cloning argument for the erasure channel)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_FTCircuit

namespace QAlgorithms.GottesmanThesis

theorem erasure_not_achievable_of_half_le (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (R : ℝ)
    (hR : 0 < R) : ¬ IsAchievableQRate (fun n => erasureChannel n p) R := by sorry

end QAlgorithms.GottesmanThesis
