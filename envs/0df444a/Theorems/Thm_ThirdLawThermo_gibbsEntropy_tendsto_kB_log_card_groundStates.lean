-- Prove2me | Theorems.Thm_ThirdLawThermo_gibbsEntropy_tendsto_kB_log_card_groundStates
-- name    : ThirdLawThermo.gibbsEntropy_tendsto_kB_log_card_groundStates
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:25:46.97099+00:00
-- url     : https://prove2.me/theorems/045f0b3d-aa8c-4fca-9681-9df0ded887a7
-- title:
--   Zero-temperature entropy equals $k_B\ln(\#\text{ground states})$
-- statement:
--   Let $\iota$ be a finite nonempty set of microstates with energies $E_i$, let $k_B>0$ be the Boltzmann constant, and write $G=\{i:E_i=\min_jE_j\}$ for the set of ground states. At temperature $T>0$ the system is in canonical equilibrium with probabilities $p_i(T)=e^{-E_i/(k_BT)}/Z(T)$, $Z(T)=\sum_je^{-E_j/(k_BT)}$, and has Gibbs entropy $S(T)=-k_B\sum_ip_i(T)\ln p_i(T)$ (see the definition file `ThirdLawThermo_Defs`).
--
--   **Theorem (statistical form of the third law).** As the temperature decreases to absolute zero, the entropy approaches a constant, namely the Boltzmann constant times the natural logarithm of the number of ground states:
--   $$\lim_{T\to0^+}S(T)=k_B\ln|G| .$$
--
--   The limit depends on the system only through the degeneracy $|G|$ of its ground state, and not on the excited energy levels; this is the precise sense in which the zero-temperature entropy is "a constant value" fixed by the ground state. When the ground state is unique the limit is $0$, and when it is degenerate the limit is the residual entropy $k_B\ln|G|>0$.
--
--   **Formalization Note** The limit is one-sided ($T\to0^+$ through $T>0$), so the junk value of the Lean definition at $T=0$ plays no role.
-- source:
--   Wikipedia, "Third law of thermodynamics", revision oldid=1369622029, https://en.wikipedia.org/w/index.php?title=Third_law_of_thermodynamics&oldid=1369622029; lead section ("the entropy of a closed system at thermodynamic equilibrium approaches a constant value when its temperature approaches absolute zero"; "there is typically one unique state (called the ground state) with minimum energy"), section "History" ("its entropy is determined only by the degeneracy of the ground state"), section "Explanation" ("the absolute entropy of any system at zero temperature is the natural log of the number of ground states times the Boltzmann constant kB").

import Definitions.Def_ThirdLawThermo_Defs
import Mathlib

open Filter Topology

namespace ThirdLawThermo

theorem gibbsEntropy_tendsto_kB_log_card_groundStates {ι : Type*} [Fintype ι] [Nonempty ι]
    (kB : ℝ) (hkB : 0 < kB) (E : ι → ℝ) :
    Tendsto (fun T => gibbsEntropy kB E T) (𝓝[>] 0)
      (𝓝 (kB * Real.log (groundStates E).card)) := by sorry

end ThirdLawThermo
