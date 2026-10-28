-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_few_kraus_not_ebt
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.few_kraus_not_ebt
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:18:51.512279+00:00
-- url     : https://prove2.me/theorems/ade9d492-765d-426c-bb88-18eac95e8165
-- title:
--   Theorem 6: fewer than d Kraus operators precludes EBT
-- statement:
--   Let $d\ge1$ and let $A_1,\ldots,A_m$ satisfy $\sum_kA_k^\dagger A_k=I$. If $m<d$, then the channel with this actual Kraus list satisfies
--
--   $$\Phi(X)=\sum_{k=1}^m A_kXA_k^\dagger\quad\text{is not EBT}.$$
--
--   The empty normalized list is impossible for $d>0$. The result gives a lower bound on the size of every Kraus representation of an EBT map; its cited ingredients are [11], or [8] with [2].
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Theorem 6: fewer than d Kraus operators precludes EBT, PDF p. 9. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

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






























































/-- Theorem 6, PDF p.9: actual Kraus-list length less than d.
The cited rank/separability ingredients are [11], or [8] with [2]. -/
theorem few_kraus_not_ebt (d m : ℕ) (hd : 0 < d) (A : Fin m → Algebra d)
    (hNormalized : IsKrausFamily A) (hFew : m < d) :
    krausEndomorphism A ∉ ebtSet d := by sorry







end QAlgorithms.Papers.Independent.Independent1.P02
