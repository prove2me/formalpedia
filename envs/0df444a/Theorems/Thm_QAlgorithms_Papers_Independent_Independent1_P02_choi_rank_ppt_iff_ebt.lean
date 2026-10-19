-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_choi_rank_ppt_iff_ebt
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.choi_rank_ppt_iff_ebt
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:18:25.721563+00:00
-- url     : https://prove2.me/theorems/5b4faab1-f62b-4bb3-bab0-f3eec9562064
-- title:
--   Lemma 7: Choi rank d makes PPT equivalent to EBT
-- statement:
--   Let $d\ge1$, let $\Phi$ be CPT, and let $J_\Phi=(\mathrm{id}\otimes\Phi)(|\beta\rangle\langle\beta|)$ for the unit maximally entangled vector $\beta=d^{-1/2}\sum_j|j,j\rangle$. If $\operatorname{rank}J_\Phi=d$, then
--
--   $$\Phi\text{ is EBT}\quad\Longleftrightarrow\quad T\circ\Phi\text{ is completely positive},$$
--
--   where $T$ is matrix transpose, a complex-linear map. The exact rank and TP hypotheses are retained; the low-rank separability ingredient is attributed to [10].
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Lemma 7: Choi rank d makes PPT equivalent to EBT, PDF p. 9. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02































































/-- Lemma 7, PDF p.9: exact Choi rank d, with low-rank ingredient [10]. -/
theorem choi_rank_ppt_iff_ebt (d : ℕ) (hd : 0 < d) (Phi : Endomorphism d)
    (hCPT : Phi ∈ cptSet d) (hRank : (choiOperator hd Phi).rank = d) :
    Phi ∈ ebtSet d ↔ Entanglement.IsCompletelyPositive ((transposeEndomorphism d).comp Phi) := by sorry






end QAlgorithms.Papers.Independent.Independent1.P02
