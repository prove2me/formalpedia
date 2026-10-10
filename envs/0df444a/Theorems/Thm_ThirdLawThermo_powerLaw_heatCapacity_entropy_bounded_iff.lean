-- Prove2me | Theorems.Thm_ThirdLawThermo_powerLaw_heatCapacity_entropy_bounded_iff
-- name    : ThirdLawThermo.powerLaw_heatCapacity_entropy_bounded_iff
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:22.978987+00:00
-- url     : https://prove2.me/theorems/35d6a524-40bc-4aea-886e-1e3ff356e242
-- title:
--   Eqs. (11)–(12): $C=C_0T^\alpha$ is compatible with the third law iff $\alpha>0$
-- statement:
--   Suppose that at low temperature the heat capacity of a sample follows a power law $C(T)=C_0T^{\alpha}$ with $C_0>0$ and $\alpha\in\mathbb R$, and fix a temperature $T>0$. The entropy difference between temperatures $T_0\in(0,T)$ and $T$ is
--   $$S(T)-S(T_0)=\int_{T_0}^{T}\frac{C(T')}{T'}\,dT'=\int_{T_0}^{T}\frac{C_0\,T'^{\alpha}}{T'}\,dT' .$$
--
--   **Theorem.** This entropy difference stays bounded above as $T_0\to0$ if and only if the exponent is positive:
--   $$\Big(\exists M\ \forall T_0\in(0,T):\ \int_{T_0}^{T}\frac{C_0T'^{\alpha}}{T'}\,dT'\le M\Big)\iff\alpha>0 .$$
--
--   Since the third law requires the entropy to approach a finite value as $T\to0$, a power-law heat capacity is compatible with it only for $\alpha>0$, in which case $C(T)\to0$ at absolute zero (Eq. (12)).
--
--   **Formalization Note** The power law is assumed to hold exactly on the whole interval $(0,T]$; the source's "asymptotically as $T\to0$" version differs only by an integral over a compact subinterval of $(0,\infty)$, which is finite. $T'^{\alpha}$ is the real power with positive base.
-- source:
--   Wikipedia, "Third law of thermodynamics", revision oldid=1369622029, https://en.wikipedia.org/w/index.php?title=Third_law_of_thermodynamics&oldid=1369622029; section "Consequences", subsection "Specific heat", Eq. (11) and Eq. (12) ("Suppose that the heat capacity of a sample in the low temperature region has the form of a power law C(T,X) = C0 T^α asymptotically as T → 0, and we wish to find which values of α are compatible with the third law. ... this integral must be bounded as T0 → 0, which is only possible if α > 0").

import Definitions.Def_ThirdLawThermo_Defs
import Mathlib

open Filter Topology

namespace ThirdLawThermo

theorem powerLaw_heatCapacity_entropy_bounded_iff (C₀ α T : ℝ) (hC₀ : 0 < C₀) (hT : 0 < T) :
    (∃ M : ℝ, ∀ T₀ ∈ Set.Ioo 0 T, ∫ t in T₀..T, C₀ * t ^ α / t ≤ M) ↔ 0 < α := by sorry

end ThirdLawThermo
