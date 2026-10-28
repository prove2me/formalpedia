-- Prove2me | Theorems.Thm_ThreeBoundQ2_orientations_complete
-- name    : ThreeBoundQ2.orientations_complete
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:38:57.675439+00:00
-- url     : https://prove2.me/theorems/ffd512fc-5a60-4c6f-9336-c824cbb37976
-- title:
--   Budget-pruned edge orientation enumeration is exhaustive
-- statement:
--   Let \(E\) be a finite list of vertex pairs, let \(d\) be a Boolean list with \(|d|=|E|\), and let \(b(v)\) be a natural-number outdegree budget. Interpret a false bit as the first-to-second orientation and a true bit as the reverse. If the resulting outgoing count satisfies
--   \[
--   \operatorname{outCount}(E,d,v)\le b(v)\qquad\text{for every }v,
--   \]
--   then \(d\) occurs in the recursive budget-pruned enumeration \(\operatorname{orientations}(b,E)\). Thus the executable search omits no orientation satisfying its stated budgets.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, Q2Enumeration, lines 88–135; source SHA256 ae08990184d0a579a04d40716428c43f0aac40ead1b50813515c656180ffe56c.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Definitions.Def_Sensitivity213303_Q2Enumeration


set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ThreeBoundQ2
end ThreeBoundQ2
open ThreeBoundQ2
variable {V : Type} [DecidableEq V]

theorem ThreeBoundQ2.orientations_complete (es : List (V × V)) (ds : List Bool) (b : V → ℕ)
    (hlen : ds.length = es.length) (hb : ∀ v, outCount es ds v ≤ b v) :
    ds ∈ orientations b es := by sorry
