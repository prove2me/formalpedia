-- Prove2me | Theorems.Thm_ShiShallow_card_coneOf_le
-- name    : ShiShallow.card_coneOf_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:03:34.012005+00:00
-- url     : https://prove2.me/theorems/e3a67e7f-02f3-4702-a921-8064b300ca6e
-- title:
--   Causal cones of depth-$d$ circuits grow by at most $2^d$
-- statement:
--   For a circuit $c$ of depth $d$ built from layers of pairwise-disjoint fan-in-$2$ gates, the causal cone of a set $S$ of wires — the set of wires that can influence $S$, obtained by propagating $S$ backwards layer by layer — satisfies
--
--   $$|\mathrm{cone}_c(S)| \;\le\; 2^{\,d}\,|S|.$$
--
--   This is the light-cone bound for shallow circuits. It follows by iterating the single-layer bound $|\mathrm{coneStep}(l,S)| \le 2|S|$ once per layer. It is the quantitative reason shallow circuits are limited: an output wire of a depth-$d$ circuit can depend on at most $2^d$ inputs, so any function genuinely depending on all $n$ inputs forces depth at least $\log_2 n$.
-- source:
--   Formalised from scratch in this development; the light-cone bound is the standard shallow-circuit argument, see e.g. Terhal--DiVincenzo, Adaptive quantum computation, constant depth quantum circuits and Arthur-Merlin games, arXiv:quant-ph/0205133.

import Definitions.Def_ShiShallow_Core

namespace ShiShallow
theorem card_coneOf_le {n : ℕ} (c : Layered n) (hc : ∀ l ∈ c, LayerOk l) (S : Finset (Fin n)) :
    (coneOf c S).card ≤ 2 ^ depth c * S.card := by sorry
end ShiShallow
