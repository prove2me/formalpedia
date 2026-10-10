-- Prove2me | Theorems.Thm_ThirdLawThermo_kB_log_two_le_zeroTemp_gibbsEntropy
-- name    : ThirdLawThermo.kB_log_two_le_zeroTemp_gibbsEntropy
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:54.471976+00:00
-- url     : https://prove2.me/theorems/6543b773-fab7-4f25-859d-bb401d9716d7
-- title:
--   Degenerate ground state: zero-temperature entropy $\ge k_B\ln 2$
-- statement:
--   Let $\iota$ be a finite nonempty set of microstates with energies $E_i$, let $k_B>0$ be the Boltzmann constant, and write $G=\{i:E_i=\min_jE_j\}$ for the set of ground states. At temperature $T>0$ the system is in canonical equilibrium with probabilities $p_i(T)=e^{-E_i/(k_BT)}/Z(T)$, $Z(T)=\sum_je^{-E_j/(k_BT)}$, and has Gibbs entropy $S(T)=-k_B\sum_ip_i(T)\ln p_i(T)$ (see the definition file `ThirdLawThermo_Defs`).
--
--   **Theorem (residual entropy of a degenerate ground state).** If the ground state is degenerate, $|G|\ge2$ (for instance the two time-reversed ground states of a system with half-integer net spin), then the entropy has a limit $S_0$ at absolute zero and this zero-point entropy is at least $k_B\ln 2$:
--   $$S_0=\lim_{T\to0^+}S(T)\ \text{exists and}\ S_0\ge k_B\ln 2 .$$
--
--   This shows that the third law does not force zero entropy at $T=0$: a non-unique ground state leaves a residual entropy.
-- source:
--   Wikipedia, "Third law of thermodynamics", revision oldid=1369622029, https://en.wikipedia.org/w/index.php?title=Third_law_of_thermodynamics&oldid=1369622029; section "Systems with non-zero entropy at absolute zero" ("An example of a system that does not have a unique ground state is one whose net spin is a half-integer, for which time-reversal symmetry gives two degenerate ground states. For such systems, the entropy at zero temperature is at least kB ln(2)").

import Definitions.Def_ThirdLawThermo_Defs
import Mathlib

open Filter Topology

namespace ThirdLawThermo

theorem kB_log_two_le_zeroTemp_gibbsEntropy {ι : Type*} [Fintype ι] [Nonempty ι]
    (kB : ℝ) (hkB : 0 < kB) (E : ι → ℝ) (hE : 2 ≤ (groundStates E).card) :
    ∃ S₀ : ℝ, Tendsto (fun T => gibbsEntropy kB E T) (𝓝[>] 0) (𝓝 S₀) ∧
      kB * Real.log 2 ≤ S₀ := by sorry

end ThirdLawThermo
