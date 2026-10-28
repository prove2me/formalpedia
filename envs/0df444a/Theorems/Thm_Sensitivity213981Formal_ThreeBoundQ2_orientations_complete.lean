-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundQ2_orientations_complete
-- name    : Sensitivity213981Formal.ThreeBoundQ2.orientations_complete
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:32:34.213827+00:00
-- url     : https://prove2.me/theorems/de1698a9-057a-4e1f-8a1e-197a466aa733
-- title:
--   Budget-pruned edge orientation enumeration is exhaustive
-- statement:
--   Let \(E\) be a finite list of vertex pairs, let \(d\) be a Boolean list with \(|d|=|E|\), and let \(b(v)\) be a natural-number outdegree budget. Interpret a false bit as the first-to-second orientation and a true bit as the reverse. If the resulting outgoing count satisfies
--   \[
--   \operatorname{outCount}(E,d,v)\le b(v)\qquad\text{for every }v,
--   \]
--   then \(d\) occurs in the recursive budget-pruned enumeration \(\operatorname{orientations}(b,E)\). Thus the executable search omits no orientation satisfying its stated budgets.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Q2Enumeration.lean, lines 88–135.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_Q2Enumeration
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundQ2.orientations_complete :
∀ {V : Type} [inst : DecidableEq.{1} V] (es : List.{0} (Prod.{0, 0} V V)) (ds : List.{0} Bool) (b : V → Nat)
  (hlen : @Eq.{1} Nat (@List.length.{0} Bool ds) (@List.length.{0} (Prod.{0, 0} V V) es))
  (hb : ∀ (v : V), @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundQ2.outCount V inst es ds v) (b v)),
  @Membership.mem.{0, 0} (List.{0} Bool) (List.{0} (List.{0} Bool)) (@List.instMembership.{0} (List.{0} Bool))
    (@Sensitivity213981Formal.ThreeBoundQ2.orientations V inst b es) ds := by sorry
