-- Prove2me | Theorems.Thm_ThornStringBits_low_energy_excitations_O_one_over_M
-- name    : ThornStringBits.low_energy_excitations_O_one_over_M
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T01:42:39.049722+00:00
-- url     : https://prove2.me/theorems/5de50e84-5040-4a05-aafb-f2d4dde2935e
-- title:
--   Low-energy excitations of the $M$-bit discretized string are $O(1/M)\times$ the two-body level spacing
-- statement:
--   Consider Thorn's discretized light-cone string (p. 4) with $M$ bits, lattice parameter $\epsilon>0$ and harmonic nearest-neighbour bonds, whose positive normal-mode angular frequencies form the set $\Omega_{M,\epsilon}$ (see the definition file). For every $M\ge 2$ and $\epsilon>0$:
--
--   1. the lowest positive excitation frequency of the $M$-bit string is
--   $$ \min\Omega_{M,\epsilon} = \frac{2}{\epsilon}\sin\frac{\pi}{M}; $$
--   2. the lowest positive excitation frequency of the two-bit system is $\min\Omega_{2,\epsilon}=\dfrac{2}{\epsilon}$;
--   3. consequently
--   $$ \min\Omega_{M,\epsilon} \;\le\; \frac{\pi}{M}\,\min\Omega_{2,\epsilon}. $$
--
--   This makes quantitative, for the harmonic Hamiltonian written in the paper, the p. 5 statement that "the low energy excitations of an $M$ particle discretized string are $O(1/M)\times$ the two-body level spacing", which is why the finite-energy excitations in the continuum limit $M\to\infty$ with $P^+=M\epsilon T_0$ fixed are those of a string.
--
--   **Formalization Note** "Two-body level spacing" is read as the lowest excitation frequency of the same cyclic chain with $M=2$ (both bonds join the same pair of bits). The paper's claim for a general, sufficiently attractive potential $V$ is not formalized; only the harmonic case exhibited in the paper is.
-- source:
--   C. B. Thorn, *Reformulating String Theory with the 1/N Expansion*, arXiv:hep-th/9405069v1 (1994; talk at the First Int. A. D. Sakharov Conf., 1991), https://arxiv.org/abs/hep-th/9405069, pp. 4–5.

import Definitions.Def_ThornStringBits_Defs
import Mathlib

open Real Matrix

namespace ThornStringBits

theorem low_energy_excitations_O_one_over_M (M : ℕ) (hM : 2 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    IsLeast (positiveModeFreqs M ε) (2 / ε * Real.sin (π / M)) ∧
    IsLeast (positiveModeFreqs 2 ε) (2 / ε) ∧
    2 / ε * Real.sin (π / M) ≤ π / M * (2 / ε) := by sorry

end ThornStringBits
