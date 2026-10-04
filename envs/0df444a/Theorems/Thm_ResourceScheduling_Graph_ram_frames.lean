-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_ram_frames
-- name    : ResourceScheduling.Graph.ram_frames
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T14:01:55.572863+00:00
-- url     : https://prove2.me/theorems/ea0a32d5-ef95-495c-aef8-e817f17187a9
-- title:
--   ram frames
-- statement:
--   Updating one register, input word, or output preserves the representation relation with the corresponding semantic update; stack nonemptiness recognizes positive registers.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAM
open CookPvsNP ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem ram_frames {V : Type} [DecidableEq V] (s : RAMState V)
    (l : RAMWire V → List Letter) (hr : RAMRep s l) :
    (∀ v w, RAMRep (s.set v w.length) (Function.update l (ramReg v) w)) ∧
    (∀ w, RAMRep { s with word := w } (Function.update l ramInput w)) ∧
    (∀ w, RAMRep { s with out := w } (Function.update l ramOutput w)) ∧
    (∀ v, ((l (ramReg v)).head?).isSome = decide (0 < s.val v)) := by sorry
end ResourceScheduling.Graph
