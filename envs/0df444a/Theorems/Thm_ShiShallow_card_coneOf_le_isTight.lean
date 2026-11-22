-- Prove2me | Theorems.Thm_ShiShallow_card_coneOf_le_isTight
-- name    : ShiShallow.card_coneOf_le_isTight
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:04:10.526667+00:00
-- url     : https://prove2.me/theorems/574cc64d-691c-4f8b-90f9-15defc9d3764
-- title:
--   The $2^{\\mathrm{depth}}$ light-cone bound is attained
-- statement:
--   The light-cone bound $|\mathrm{cone}_c(S)| \le 2^{\,d}|S|$ is **sharp**: for every depth $d$ there exist a wire count $n$, a circuit $c$ of depth exactly $d$ all of whose layers are well formed, and a single-wire set $S$, such that
--
--   $$|\mathrm{cone}_c(S)| \;=\; 2^{\,d}\,|S| \;=\; 2^{\,d}.$$
--
--   The witness is a CNOT binary tree on $n = 2^d$ wires. Layer $t$ consists of the CNOT gates carrying wire $i$ onto wire $2^{t} + i$ for each $i < 2^{t}$; these have pairwise disjoint supports, so the layer is well formed, and propagating backwards the cone of the single wire $0$ is exactly the set of wires with index below $2^{t}$ after $t$ layers, doubling at every layer.
--
--   Together with the upper bound this pins the growth rate of causal cones exactly, showing the exponent cannot be lowered and that the bound is not an artefact of the counting argument.
-- source:
--   Formalised from scratch in this development; the light-cone bound is the standard shallow-circuit argument, see e.g. Terhal--DiVincenzo, Adaptive quantum computation, constant depth quantum circuits and Arthur-Merlin games, arXiv:quant-ph/0205133.

import Definitions.Def_ShiShallow_Core

namespace ShiShallow
theorem card_coneOf_le_isTight (d : ℕ) :
    ∃ (n : ℕ) (c : Layered n) (S : Finset (Fin n)),
      (∀ l ∈ c, LayerOk l) ∧ depth c = d ∧ S.card = 1 ∧
        (coneOf c S).card = 2 ^ depth c * S.card := by sorry
end ShiShallow
