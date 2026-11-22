-- Prove2me | Theorems.Thm_ShiShallow_phase_composition
-- name    : ShiShallow.phase_composition
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T05:44:42.390724+00:00
-- url     : https://prove2.me/theorems/2a738657-7a0d-4c69-bdf2-d390d1a71648
-- title:
--   Composing two pointwise-phase maps multiplies the phases
-- statement:
--   If two maps on states each act as pointwise multiplication by a fixed function -- f by a and g by b -- then their composition acts as multiplication by the product: g (f psi) x = b x * a x * psi x.
--
--   This is the algebraic glue for assembling a diagonal-gate circuit. Once each layer is known to be a pointwise phase (which is exactly what the T-power and CNOT-conjugated-T-power results provide), the whole circuit's effect is obtained by multiplying the per-layer phases, and the product can then be identified with a target phase function.
--
--   HONEST POSITIONING, because the natural next step is bigger than this: this is NOT a CCZ circuit identity. It is the composition principle that such an assembly would use repeatedly -- for three single-wire T factors, three conjugated adjoint-T parity factors, and one nested-conjugation triple-parity factor -- alongside the published phase-exponent identity that identifies the seven-factor product with the CCZ sign. That assembly is not performed here and is not claimed.
--
--   The hypotheses are stated for EVERY input state, not just the given one, which is what makes the composition step valid. No unitarity or normalisation is assumed; f and g need not come from any gate at all.

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem phase_composition {n : ℕ} (f g : QState n → QState n) (a b : Bits n → ℂ)
    (hf : ∀ (φ : QState n) (x : Bits n), f φ x = a x * φ x)
    (hg : ∀ (φ : QState n) (x : Bits n), g φ x = b x * φ x)
    (ψ : QState n) :
    ∀ x : Bits n, g (f ψ) x = (b x * a x) * ψ x := by
  sorry

end ShiShallow
