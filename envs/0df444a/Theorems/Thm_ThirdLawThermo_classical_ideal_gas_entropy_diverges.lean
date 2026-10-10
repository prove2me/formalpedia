-- Prove2me | Theorems.Thm_ThirdLawThermo_classical_ideal_gas_entropy_diverges
-- name    : ThirdLawThermo.classical_ideal_gas_entropy_diverges
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:42.467403+00:00
-- url     : https://prove2.me/theorems/e44092ea-aa53-4403-ad17-a323217dd4a5
-- title:
--   Eq. (13): a classical ideal gas with $C_V=\tfrac32R$ violates the third law
-- statement:
--   The molar heat capacity at constant volume of a monatomic classical ideal gas is the constant $C_V=\tfrac32R$, where $R>0$ is the molar gas constant. Fix $T>0$.
--
--   **Theorem.** The molar entropy difference between $T_0$ and $T$ diverges as $T_0\to0$:
--   $$S(T)-S(T_0)=\int_{T_0}^{T}\frac{\tfrac32R}{t}\,dt\longrightarrow+\infty\qquad(T_0\to0^+).$$
--
--   So a gas with constant heat capacity all the way down to absolute zero contradicts the third law; the source resolves the conflict by quantum statistics (Fermi–Dirac and Bose–Einstein gases) at low temperature.
-- source:
--   Wikipedia, "Third law of thermodynamics", revision oldid=1369622029, https://en.wikipedia.org/w/index.php?title=Third_law_of_thermodynamics&oldid=1369622029; section "Consequences", subsection "Specific heat", Eq. (13) ("the molar specific heat at constant volume of a monatomic classical ideal gas ... is given by CV = 3/2 R ... We can verify this more fundamentally by substituting CV in Eq. (14), which yields (13). In the limit T0 → 0 this expression diverges, again contradicting the third law of thermodynamics").

import Definitions.Def_ThirdLawThermo_Defs
import Mathlib

open Filter Topology

namespace ThirdLawThermo

theorem classical_ideal_gas_entropy_diverges (R T : ℝ) (hR : 0 < R) (hT : 0 < T) :
    Tendsto (fun T₀ => ∫ t in T₀..T, (3 / 2 * R) / t) (𝓝[>] 0) atTop := by sorry

end ThirdLawThermo
