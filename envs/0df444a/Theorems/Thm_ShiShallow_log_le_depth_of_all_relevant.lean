-- Prove2me | Theorems.Thm_ShiShallow_log_le_depth_of_all_relevant
-- name    : ShiShallow.log_le_depth_of_all_relevant
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:03:37.951351+00:00
-- url     : https://prove2.me/theorems/3d656749-1d9a-43aa-a791-592ceb1781ad
-- title:
--   A circuit reaching all $n$ inputs has depth at least $\\log_2 n$
-- statement:
--   The logarithmic form of the light-cone depth bound. For a layered circuit of pairwise-disjoint fan-in-$2$ gates on $n$ inputs and $m$ ancillas, if every input wire lies in the causal cone of the designated output wire then
--
--   $$\log_2 n \;\le\; \mathrm{depth}(c).$$
--
--   This is the shape in which circuit lower bounds are usually quoted: connecting $n$ inputs to a single output through gates of fan-in $2$ requires logarithmically many layers, since each additional layer can at most double the reachable set.
-- source:
--   Formalised from scratch in this development; the light-cone bound is the standard shallow-circuit argument, see e.g. Terhal--DiVincenzo, Adaptive quantum computation, constant depth quantum circuits and Arthur-Merlin games, arXiv:quant-ph/0205133.

import Definitions.Def_ShiShallow_Core

namespace ShiShallow
theorem log_le_depth_of_all_relevant {n m : ℕ} (c : Layered (n + m))
    (out : Fin (n + m)) (hc : ∀ l ∈ c, LayerOk l)
    (hall : ∀ i : Fin n, Fin.castAdd m i ∈ coneOf c {out}) :
    Nat.log 2 n ≤ depth c := by sorry
end ShiShallow
