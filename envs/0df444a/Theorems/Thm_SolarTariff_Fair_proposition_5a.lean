-- Prove2me | Theorems.Thm_SolarTariff_Fair_proposition_5a
-- name    : SolarTariff.Fair.proposition_5a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:23.589994+00:00
-- url     : https://prove2.me/theorems/f9cf7e47-897b-45c2-8ac8-590583f3ca73
-- title:
--   Proposition 5(a), p. 18 — T* feasibly induces the target outcome
-- statement:
--   Consider a finite market satisfying the standing conditions, and a target outcome $A$ in which at least one tier adopts and $\Delta_E^A\le E^0$. The constructed tariff $T^*$ feasibly induces that outcome at solar price $t(m)$:
--
--   $$A(t(m))=A,\qquad \Pi_S(t(m))=\Delta_S>\Pi_S(p)\ \text{for every }p\ne t(m),\qquad \Delta\Pi_U=\Delta_U.$$
--
--   Thus the solar company has the prescribed price as its unique best response, and the utility meets its required profit change. This is the feasibility part of Proposition 5 and supplies the equilibrium assertion used in the combined goal.
--
--   **Formalization Note** The paper's ordering $o$ is suppressed because $T^*$ gives all adopting tiers the same threshold and all nonadopting tiers a lower one. Solar prices range over every real number. The standing predicate makes explicit $h_i,d_i,g_i>0$; equations (17) and (19) are read through the induced equilibrium because their printed indexing conflicts with (11)–(13).
-- source:
--   Singh & Scheller-Wolf, That’s Not Fair: Tariff Structures for Electric Utilities with Rooftop Solar, SSRN 2926676 (SSRN Version), p. 18 (PDF 18), Proposition 5(a) and T* construction; p. S.3 (PDF 35), proof

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

namespace SolarTariff.Fair

theorem proposition_5a {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Market ι) (hM : M.Standing) (A : Finset ι)
    (hA : Admissible M A) :
    FeasibleP2 M A ((TStar M A).bills M) (tm M A) := by sorry

end SolarTariff.Fair
