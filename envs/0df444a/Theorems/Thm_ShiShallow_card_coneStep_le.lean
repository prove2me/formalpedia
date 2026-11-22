-- Prove2me | Theorems.Thm_ShiShallow_card_coneStep_le
-- name    : ShiShallow.card_coneStep_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:03:56.686223+00:00
-- url     : https://prove2.me/theorems/9780af22-2bfd-4cf1-a8e1-419d47ec4acc
-- title:
--   A well-formed layer at most doubles a causal cone
-- statement:
--   Let $S$ be a set of wires of an $n$-wire quantum circuit and let $l$ be a single **layer**, that is, a list of gates acting on pairwise disjoint wires (`LayerOk`). Propagating $S$ backwards through $l$ adjoins the support of every gate of $l$ that touches $S$. The resulting set satisfies
--
--   $$|\mathrm{coneStep}(l, S)| \;\le\; 2\,|S|.$$
--
--   The bound is the elementary counting step underlying all light-cone arguments for shallow circuits: since the gate set has fan-in at most $2$, each wire of $S$ can drag in at most one new wire, and disjointness of supports within the layer prevents any gate from being counted twice. The hypothesis that the layer is well formed is essential — for a layer whose gates share wires, gates can chain within the layer and the conclusion fails.
-- source:
--   Formalised from scratch in this development; the light-cone bound is the standard shallow-circuit argument, see e.g. Terhal--DiVincenzo, Adaptive quantum computation, constant depth quantum circuits and Arthur-Merlin games, arXiv:quant-ph/0205133.

import Definitions.Def_ShiShallow_Core

namespace ShiShallow
theorem card_coneStep_le {n : ℕ} (l : List (Instr n)) (hl : LayerOk l) (S : Finset (Fin n)) :
    (coneStep l S).card ≤ 2 * S.card := by sorry
end ShiShallow
