-- Prove2me | Theorems.Thm_SensitivityRankedConstruction_gate_nested
-- name    : SensitivityRankedConstruction.gate_nested
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:48:49.939612+00:00
-- url     : https://prove2.me/theorems/50745c56-6f9e-4e19-ba95-d21b1399bdff
-- title:
--   Nested child families give nested gate families
-- statement:
--   Let a colored child family $F$ be nested, and let a gate recipe satisfy its nesting conditions: antitone guard cutoffs and a compatible downward transport of allowed target assignments. For any guard family,
--   $$
--   i\le j\quad\Longrightarrow\quad
--   G_v(j,x)\Longrightarrow G_v(i,x).
--   $$
--   Thus the parent family $G$ is nested.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/GateInvariants.lean lines 68–91; SHA256 203148c2a2707c40a0d239913f4dc7b44ef2cce2545e7545006824d075c324e5; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_GateInvariants
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-!
# Nesting and strict identities of the actual gates

The finite recipe conditions below describe every possible pair of soft guard
counts at two grades. They include the extra zero-count information supplied
by a hard cutoff, so the warm rows can be checked without replacing their
semantics by a stronger condition.
-/
open SensitivityRankedConstruction
open scoped Classical

theorem SensitivityRankedConstruction.gate_nested {V S I Color : Type} {L : ℕ}
    {row : RowFamily I Color L} (hnested : Nested row)
    (guards : GuardFamily V S) {recipe : GateRecipe S L}
    (hrecipe : RecipeNesting recipe) : Nested (gateRow row guards recipe) := by sorry
