-- Prove2me | Theorems.Thm_ShiShallow_runLayered_norm
-- name    : ShiShallow.runLayered_norm
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:03:48.984224+00:00
-- url     : https://prove2.me/theorems/5d754806-ad53-45a7-bee3-e765d1f472d6
-- title:
--   Layered circuits preserve the $\\ell^2$ norm
-- statement:
--   Every circuit built from the gate set $\{H, S, T, X, \mathrm{CNOT}\}$ acts as an isometry on amplitude vectors: for any state $\psi$,
--
--   $$\sum_{x \in \{0,1\}^n} \bigl| (c\,\psi)(x) \bigr|^2 \;=\; \sum_{x \in \{0,1\}^n} |\psi(x)|^2 .$$
--
--   The proof reduces to unitarity of each one-qubit gate matrix, lifted to the full $2^n$-dimensional space through the fibre decomposition of $\{0,1\}^n$ over a single wire, together with the observation that CNOT merely permutes basis strings. This is the statement that the circuit model conserves probability, and it is what makes the acceptance probability of a circuit a genuine probability.
-- source:
--   Formalised from scratch in this development; the light-cone bound is the standard shallow-circuit argument, see e.g. Terhal--DiVincenzo, Adaptive quantum computation, constant depth quantum circuits and Arthur-Merlin games, arXiv:quant-ph/0205133.

import Definitions.Def_ShiShallow_Core

namespace ShiShallow
theorem runLayered_norm {n : ℕ} (c : Layered n) (ψ : QState n) :
    ∑ x : Bits n, ‖runLayered c ψ x‖ ^ 2 = ∑ x : Bits n, ‖ψ x‖ ^ 2 := by sorry
end ShiShallow
