-- Prove2me | Theorems.Thm_ThirdLawThermo_gibbsEntropy_tendsto_zero_of_unique_groundState
-- name    : ThirdLawThermo.gibbsEntropy_tendsto_zero_of_unique_groundState
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:26:20.188178+00:00
-- url     : https://prove2.me/theorems/6a963324-5e0e-4d68-be2c-fc26dfbfc1dd
-- title:
--   Unique ground state $\Rightarrow$ entropy tends to $0$ at absolute zero
-- statement:
--   Let $\iota$ be a finite nonempty set of microstates with energies $E_i$, let $k_B>0$ be the Boltzmann constant, and write $G=\{i:E_i=\min_jE_j\}$ for the set of ground states. At temperature $T>0$ the system is in canonical equilibrium with probabilities $p_i(T)=e^{-E_i/(k_BT)}/Z(T)$, $Z(T)=\sum_je^{-E_j/(k_BT)}$, and has Gibbs entropy $S(T)=-k_B\sum_ip_i(T)\ln p_i(T)$ (see the definition file `ThirdLawThermo_Defs`).
--
--   **Theorem (unique ground state, perfect crystal).** If the ground state is unique, $|G|=1$, then the entropy tends to zero at absolute zero:
--   $$\lim_{T\to0^+}S(T)=0 .$$
--
--   This is the case of a perfect crystal singled out by Planck's and Lewis–Randall's formulations: with a single accessible microstate at $T=0$, the entropy at absolute zero is exactly $k_B\ln 1=0$.
-- source:
--   Wikipedia, "Third law of thermodynamics", revision oldid=1369622029, https://en.wikipedia.org/w/index.php?title=Third_law_of_thermodynamics&oldid=1369622029; lead section ("there is typically one unique state (called the ground state) with minimum energy. In such a case, the entropy at absolute zero will be exactly zero"), section "Explanation" ("The entropy of a perfect crystal lattice as defined by Nernst\'s theorem is zero provided that its ground state is unique, because ln(1) = 0").

import Definitions.Def_ThirdLawThermo_Defs
import Mathlib

open Filter Topology

namespace ThirdLawThermo

theorem gibbsEntropy_tendsto_zero_of_unique_groundState {ι : Type*} [Fintype ι] [Nonempty ι]
    (kB : ℝ) (hkB : 0 < kB) (E : ι → ℝ) (hE : (groundStates E).card = 1) :
    Tendsto (fun T => gibbsEntropy kB E T) (𝓝[>] 0) (𝓝 0) := by sorry

end ThirdLawThermo
