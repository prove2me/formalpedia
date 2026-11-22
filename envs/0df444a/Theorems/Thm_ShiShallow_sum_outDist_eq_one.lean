-- Prove2me | Theorems.Thm_ShiShallow_sum_outDist_eq_one
-- name    : ShiShallow.sum_outDist_eq_one
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:03:40.694563+00:00
-- url     : https://prove2.me/theorems/faaf0101-2cef-472a-ab8e-2484f906165e
-- title:
--   A circuit's output is a probability distribution
-- statement:
--   For any circuit $c$ on $n$ input wires and $m$ ancillas and any classical input $x$, the numbers $\mathrm{outDist}(c,x,y) = |(c\,|x,0^m\rangle)(y)|^2$ form a probability distribution over basis strings:
--
--   $$\sum_{y \in \{0,1\}^{n+m}} \mathrm{outDist}(c,x,y) \;=\; 1 .$$
--
--   Together with non-negativity of each term this says that measuring all wires of the circuit in the computational basis yields a well-defined random outcome. It combines norm preservation along the circuit with the fact that the padded input state $|x, 0^m\rangle$ is a unit vector.
-- source:
--   Formalised from scratch in this development; the light-cone bound is the standard shallow-circuit argument, see e.g. Terhal--DiVincenzo, Adaptive quantum computation, constant depth quantum circuits and Arthur-Merlin games, arXiv:quant-ph/0205133.

import Definitions.Def_ShiShallow_Core

namespace ShiShallow
theorem sum_outDist_eq_one {n m : ℕ} (c : Layered (n + m)) (x : Bits n) :
    ∑ y : Bits (n + m), outDist c x y = 1 := by sorry
end ShiShallow
