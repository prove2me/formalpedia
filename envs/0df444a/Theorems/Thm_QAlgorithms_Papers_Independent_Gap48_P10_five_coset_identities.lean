-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_five_coset_identities
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.five_coset_identities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:15:39.988919+00:00
-- url     : https://prove2.me/theorems/3f3b734f-54b5-4b33-8a92-5a4a77be071e
-- title:
--   Lemma 2.2: five coset identities
-- statement:
--   Let $\mathcal C=\langle H,S,\omega I\rangle$, $\mathcal S=\langle S,X,\omega I\rangle$, $\mathcal C'=\mathcal C\setminus\mathcal S$, $\mathcal H=\{I,H,SH\}$, and $\mathcal H'=\{H,SH\}$. For sets of matrices, juxtaposition means the set of all products. Then
--
--   $$
--   \mathcal C=\mathcal H\mathcal S,\quad
--   \mathcal C'=\mathcal H'\mathcal S,\quad
--   \mathcal S\mathcal H'\subseteq\mathcal H'\mathcal S,\quad
--   \mathcal S T=T\mathcal S,\quad
--   T\mathcal S T=\mathcal S.
--   $$
--   These are set identities and an inclusion for the finite, phase-sensitive groups used by normalization.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 2, Lemma 2.2: five coset identities

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Lemma 2.2, equations (3)-(7), PDF p.2. All five operations are on SETS;
smallSet is the calligraphic subgroup, not the single S gate. -/
theorem five_coset_identities :
    cliffordSet = transversal * smallSet ∧
    cliffordSet \ smallSet = nonidentityTransversal * smallSet ∧
    smallSet * nonidentityTransversal ⊆ nonidentityTransversal * smallSet ∧
    smallSet * {QAlgorithms.gateT} = {QAlgorithms.gateT} * smallSet ∧
    ({QAlgorithms.gateT} * smallSet) * {QAlgorithms.gateT} = smallSet := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
