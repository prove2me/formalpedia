-- Prove2me | Theorems.Thm_ThreeSum_Auxiliary_moduli_card
-- name    : ThreeSum.Auxiliary.moduli_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:22:55.794999+00:00
-- url     : https://prove2.me/theorems/676d43a3-44b9-48aa-91e7-66fb6d0ee335
-- title:
--   Auxiliary: moduli card
-- statement:
--   The Auxiliary construction uses the moduli card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Auxiliary.lean#L21-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Auxiliary.lean#L21-L22

import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas
import Definitions.Def_Submission_ThreeSum_Auxiliary
set_option autoImplicit false
open ThreeSum ThreeSum.Auxiliary
open Finset
open scoped BigOperators

theorem ThreeSum.Auxiliary.moduli_card (C : Finset ℕ) : (moduli C).card = C.card := by sorry
