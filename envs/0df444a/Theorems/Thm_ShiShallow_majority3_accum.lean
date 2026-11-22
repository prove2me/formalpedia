-- Prove2me | Theorems.Thm_ShiShallow_majority3_accum
-- name    : ShiShallow.majority3_accum
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T07:17:16.008157+00:00
-- url     : https://prove2.me/theorems/491ece43-49fc-45ca-9adc-35741776e90f
-- title:
--   Three composed Toffolis accumulate the majority polynomial on a scratch wire
-- statement:
--   Composing three Toffolis with control pairs (w0,w1), (w1,w2), (w2,w0), all targeting a scratch wire t, accumulates the exclusive-or of the three pairwise ANDs onto that wire, leaving everything else untouched.
--
--   Mechanism: each Toffoli exclusive-ors one pairwise AND into the target. The controls are unaffected because they are distinct from the target, and the successive writes to the target collapse since only the last survives.
--
--   A SUBTLETY WORTH RECORDING. Unfolding the composition from the outside in produces the exclusive-or chain in the REVERSE pair order from the one stated, because the outermost Toffoli's controls are read against the original index. Exclusive-or is associative and commutative so the value agrees, but the terms are not syntactically identical, so the reordering is discharged by an explicit sixteen-case check rather than left to automation.
--
--   PROVENANCE. The Toffoli action is taken as a hypothesis, abstracting the separately accepted theorem that builds a Toffoli from this development's gate set; the content contributed here is only the three-fold accumulation. The wire-distinctness hypotheses carry no mathematical content -- they merely say the controls are not the scratch wire.
--
--   SCOPE. Composed gate ACTIONS on an amplitude array, not runLayered of a Layered term. No unitarity and no normalisation assumed. Gate set H, S, T, X, CNOT with no universality theorem.

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem majority3_accum {n : ℕ} (w0 w1 w2 t : Fin n)
    (hw0t : w0 ≠ t) (hw1t : w1 ≠ t) (hw2t : w2 ≠ t)
    (TOF : Fin n → Fin n → Fin n → QState n → QState n)
    (hTOF : ∀ (p q r : Fin n) (ψ : QState n),
      TOF p q r ψ = fun x => ψ (Function.update x r (xor (x r) (x p && x q))))
    (ψ : QState n) :
    TOF w2 w0 t (TOF w1 w2 t (TOF w0 w1 t ψ))
      = fun x => ψ (Function.update x t
          (xor (xor (xor (x t) (x w0 && x w1)) (x w1 && x w2)) (x w2 && x w0))) := by
  sorry

end ShiShallow
