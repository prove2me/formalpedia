-- Prove2me | Theorems.Thm_Wigner_fock_wigner_neg
-- name    : Wigner.fock_wigner_neg
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T16:51:36.325457+00:00
-- url     : https://prove2.me/theorems/ee403829-3830-4313-ac7a-6bb8f4f3c185
-- title:
--   Negativity of the Wigner function at the origin: first Fock state
-- statement:
--   A concrete witness of negativity: the Wigner function of the first excited Fock state is negative at the origin. In the same dimensionless units as Groenewold's formula ($\hbar = 1$),
--
--   $$W_{|1\rangle}(0,0) = -\frac{1}{\pi} < 0.$$
--
--   The source text introduces the Wigner distribution as one that "can and normally does take on negative values for states which have no classical model", marking quantum-mechanical interference; the first excited number state at the origin is its most compact explicit witness.
--
--   **Formalization Note** The statement fixes the wavefunction (the first normalized Hermite function), the Planck-constant slot to $1$, and the phase-space point to the origin; there are no hypotheses.
-- source:
--   Wikipedia, "Wigner quasiprobability distribution" (oldid 1376057304), section "Relation to classical mechanics" (negativity of W) and section "Examples" (Fock states). https://en.wikipedia.org/wiki/Wigner_quasiprobability_distribution

import Mathlib
import Definitions.Def_wigner
import Definitions.Def_wigner_states

open MeasureTheory

namespace Wigner

theorem fock_wigner_neg : wigner (fockState 1) 1 0 0 < 0 := by sorry

end Wigner
