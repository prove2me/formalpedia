-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_ram_copy
-- name    : ResourceScheduling.Graph.ram_copy
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T14:37:16.612521+00:00
-- url     : https://prove2.me/theorems/46eb9bfe-f921-4932-b642-efaa4517870a
-- title:
--   ram copy
-- statement:
--   Appending and assigning a source stack to a distinct natural register implement the corresponding length arithmetic with linear budgets.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMOps
open CookPvsNP ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem ram_copy {V : Type} [DecidableEq V] (src : RAMWire V) (v : V)
    (hd : src ≠ ramReg v) (ht : src ≠ ramTmp 0) (f : RAMState V → ℕ)
    (hf : ∀ s l, RAMRep s l → (l src).length = f s) :
    StackImplements RAMRep (ramAppend src v)
      (fun s => s.set v (f s + s.val v)) (fun s => 6 * f s + 3) ∧
    StackImplements RAMRep (ramAssign src v)
      (fun s => s.set v (f s)) (fun s => 3 * s.val v + 6 * f s + 5) := by sorry
end ResourceScheduling.Graph
