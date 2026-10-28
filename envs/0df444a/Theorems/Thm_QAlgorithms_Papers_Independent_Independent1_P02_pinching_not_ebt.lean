-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_pinching_not_ebt
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.pinching_not_ebt
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:18:29.208092+00:00
-- url     : https://prove2.me/theorems/d7df3507-eebd-4923-be56-a0535b09bea0
-- title:
--   Section 3: nontrivial block-diagonal projection preserves entanglement
-- statement:
--   Let $d\ge1$ and let $E_1,\ldots,E_m$ be a von Neumann measurement: mutually orthogonal Hermitian projections summing to $I$. If some $E_k$ has rank greater than one, then
--
--   $$\Phi(X)=\sum_k E_kXE_k\quad\text{is not EBT}.$$
--
--   The actual computed pinching map is used. A rank-two block can retain entanglement, distinguishing such block projections from rank-one dephasing.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Section 3: nontrivial block-diagonal projection preserves entanglement, PDF p. 9. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

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





























































/-- Section 3, PDF p.9: a block pinching with a rank>1 block is not EBT. -/
theorem pinching_not_ebt (d m : ℕ) (hd : 0 < d) (E : Fin m → Algebra d)
    (hHermitian : ∀ k, (E k).IsHermitian) (hProjection : ∀ k, E k * E k = E k)
    (hOrthogonal : ∀ j k, j ≠ k → E j * E k = 0) (hComplete : ∑ k, E k = 1)
    (hLarge : ∃ k, 1 < (E k).rank) :
    krausEndomorphism E ∉ ebtSet d := by sorry








end QAlgorithms.Papers.Independent.Independent1.P02
