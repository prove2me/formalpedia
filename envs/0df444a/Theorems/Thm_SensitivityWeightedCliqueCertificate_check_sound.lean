-- Prove2me | Theorems.Thm_SensitivityWeightedCliqueCertificate_check_sound
-- name    : SensitivityWeightedCliqueCertificate.check_sound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:22.889986+00:00
-- url     : https://prove2.me/theorems/5a5f9163-abec-4285-88e1-bd4c0d96db03
-- title:
--   Soundness of weighted branch-and-color clique certificates
-- statement:
--   Let adjacency and nonnegative integer vertex weights be encoded on natural-number vertices. If the weighted certificate checker accepts a certificate for mask $M$ and bound $B$, then every finite clique $K$ whose vertices belong to $M$ satisfies
--
--   $$\sum_{v\in K}w(v)\le B.$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/WeightedCliqueCertificate.lean lines 96–121; SHA256 72037be65f9252ea0e5fab90db142b411b84bef23fde2c287be9bddd815bedc9; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CliqueCertificate
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_WeightedCliqueCertificate
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.Bitwise

namespace SensitivityCliqueCertificate
end SensitivityCliqueCertificate
namespace SensitivityWeightedCliqueCertificate
end SensitivityWeightedCliqueCertificate


/-! The same explicit branch/coloring proof objects with nonnegative vertex weights. -/
open SensitivityWeightedCliqueCertificate
open scoped BigOperators
open SensitivityCliqueCertificate
set_option autoImplicit false

theorem SensitivityWeightedCliqueCertificate.check_sound (adj weight : ℕ → ℕ) (certificate : Certificate)
    (mask bound : ℕ) (hcheck : check adj weight mask bound certificate = true)
    (vertices : Finset ℕ) (hmask : InMask mask vertices) (hclique : Clique adj vertices) :
    (∑ v ∈ vertices, weight v) ≤ bound := by sorry
