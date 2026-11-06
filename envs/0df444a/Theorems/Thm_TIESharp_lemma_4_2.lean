-- Prove2me | Theorems.Thm_TIESharp_lemma_4_2
-- name    : TIESharp.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:39:21.102506+00:00
-- url     : https://prove2.me/theorems/aa486ac1-1348-45f9-9fd8-48b5515ad954
-- title:
--   Lemma 4.2 — consistency under adding free jobs
-- statement:
--   Let $n\ge2$. Every feasible truthful-in-expectation $R$-approximate family admits a feasible truthful-in-expectation $R$-approximate replacement that is invariant under job and machine relabeling and has the following property: if a column has a zero entry, it is assigned only to zero-cost machines, and deleting it preserves the entire retained assignment distribution and the normalized expected payments.
--
--   The replacement makes padding by a free job (one with a zero-cost machine) invisible to the original jobs. This is what later allows the limiting assignment probabilities at different job counts to be compared.
--
--   Differences from the source:
--   - encoding: invariant under job and machine relabeling → IsJobEquivariant and IsMachineEquivariant on assignment weights and payments; reason: the paper's replacement carries the normalized payments p̄ = t·q − V, which are equivariant because its laws and potentials are
--   - encoding: a family: one assignment distribution and one finite expected-payment vector per job count, on bids in [0,∞)^{n×m} → Family n with real weights alloc and real payments pay, plus IsFeasible (weights nonnegative and summing to one at every nonnegative bid profile); values at profiles with a negative entry are unconstrained; reason: Lean convention for a distribution on the finite set of assignments; same families
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 4.2, p.14 (n ≥ 2 from §4, p.13)

import Mathlib
import Definitions.Def_TIESharp_IsFeasible
import Definitions.Def_TIESharp_IsTIE
import Definitions.Def_TIESharp_IsRApprox
import Definitions.Def_TIESharp_IsConsistentFamily

set_option autoImplicit false

namespace TIESharp

/-- **Lemma 4.2 (Consistency under adding free jobs)** (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, Lemma 4.2, p.14). Let `n ≥ 2` (standing
assumption of §4, p.13: "Fix n ≥ 2"). Every feasible truthful-in-expectation `R`-approximate family
admits a feasible truthful-in-expectation `R`-approximate replacement that is invariant under job and
machine relabeling and has the following property: if a column has a zero entry, it is assigned
only to zero-cost machines, and deleting it preserves the entire retained assignment distribution
and the normalized expected payments (`IsConsistentFamily`).

**Formalization Note.** The relabeling invariance is stated on allocations and payments; the
paper's replacement family carries the normalized payments, which are equivariant. -/
theorem lemma_4_2 (n : ℕ) (hn : 2 ≤ n) (F : Family n) (R : ℝ) (hF : IsFeasible F)
    (hT : IsTIE F) (hR : IsRApprox F R) :
    ∃ F' : Family n, IsFeasible F' ∧ IsTIE F' ∧ IsRApprox F' R ∧ IsConsistentFamily F' := by sorry

end TIESharp
