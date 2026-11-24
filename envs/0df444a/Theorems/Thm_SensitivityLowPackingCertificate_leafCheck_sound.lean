-- Prove2me | Theorems.Thm_SensitivityLowPackingCertificate_leafCheck_sound
-- name    : SensitivityLowPackingCertificate.leafCheck_sound
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:22:52.75484+00:00
-- url     : https://prove2.me/theorems/6a857a0e-5476-4619-8cb3-3cd327c9ca03
-- title:
--   Soundness of a low-one packing certificate leaf
-- statement:
--   Let a finite packing graph pass its compatibility check. Let a partial assignment fix only graph vertices and agree with a feasible multiplicity function and designated zero set. Suppose the leaf checker accepts weighted-clique and zero-clique certificates together with its numerical bounds $(K,Z_0)$. Then every such feasible extension satisfies
--
--   $$\sum_v n_v+|Z|\le K,\qquad |Z|\le Z_0.$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/LowPackingCertificate.lean lines 143–189; SHA256 9369710d4b37528ce9d43825665df5aca623b38f242b1f3f08a0c5362829c88c; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CliqueCertificate
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_LowPackingCertificate
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

namespace SensitivityCliqueCertificate
end SensitivityCliqueCertificate
namespace SensitivityLowPacking
end SensitivityLowPacking
namespace SensitivityLowPackingCertificate
end SensitivityLowPackingCertificate


/-! A finite certificate for the low-one packing problem.  Branches assign an
actual macro multiplicity in {0,1,2,3}; leaves prove weighted independence and
zero-population bounds on the remaining possible macros. -/
open SensitivityLowPackingCertificate
open scoped BigOperators
open SensitivityLowPacking SensitivityCliqueCertificate
set_option autoImplicit false
open scoped Classical

theorem SensitivityLowPackingCertificate.leafCheck_sound (g : Graph) (hg : graphCheck g = true) (state : State)
    (count : ℕ → ℕ) (zeros : Finset ℕ) (hf : state.fixed ⊆ g.vertices.toFinset)
    (ha : Agrees state count) (hfit : Fits g count zeros)
    (total zero alpha zeroAlpha : ℕ) (weightCert zeroCert : Certificate)
    (hc : leafCheck g state total zero alpha zeroAlpha weightCert zeroCert = true) :
    (∑ v ∈ g.vertices.toFinset, count v) + zeros.card ≤ total ∧ zeros.card ≤ zero := by sorry
