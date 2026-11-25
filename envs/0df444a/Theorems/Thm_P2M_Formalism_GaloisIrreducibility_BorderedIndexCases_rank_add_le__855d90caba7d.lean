-- Prove2me | Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_rank_add_le__855d90caba7d
-- name    : P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_rank_add_le__855d90caba7d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:15.522216+00:00
-- url     : https://prove2.me/theorems/1c4e660a-3cf1-41c7-9a8a-e7ed15761c2c
-- title:
--   P2 M Formalism Galois Irreducibility Bordered Index Cases rank add le  855d90caba7d: P2 M Formalism Galois Irreducibility Bordered Index Cases rank add le  855d90caba7d
-- statement:
--   The P2 M Formalism Galois Irreducibility Bordered Index Cases rank add le  855d90caba7d construction uses the P2 M Formalism Galois Irreducibility Bordered Index Cases rank add le  855d90caba7d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L62-L67

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Matrix
open Formalism.GaloisIrreducibility.BorderedIndexCases
variable {R : Type} [CommRing R]

theorem P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_rank_add_le__855d90caba7d {K : Type} [Field K] {m : ℕ} (A B : Matrix (Fin m) (Fin m) K) :
    (A + B).rank ≤ A.rank + B.rank := by sorry

alias «Formalism».«GaloisIrreducibility».«BorderedIndexCases».«rank_add_le'» := P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_rank_add_le__855d90caba7d
