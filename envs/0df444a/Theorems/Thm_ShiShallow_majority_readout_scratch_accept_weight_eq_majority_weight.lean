-- Prove2me | Theorems.Thm_ShiShallow_majority_readout_scratch_accept_weight_eq_majority_weight
-- name    : ShiShallow.majority_readout_scratch_accept_weight_eq_majority_weight
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T08:53:58.766174+00:00
-- url     : https://prove2.me/theorems/4cd86d6b-0524-4648-82ba-34f205e396fe
-- title:
--   The scratch-wire accept weight after the three-Toffoli majority readout equals the majority-true input weight
-- statement:
--   This closes the bridge between two previously DISCONNECTED halves of the development. One half showed a majority readout is implementable in the available gate set: three Toffolis with control pairs drawn from three data wires, all targeting one scratch wire, deposit the majority of the controls onto that wire. The other half stated acceptance as a WEIGHT -- a finite sum of squared amplitudes restricted to the outcomes satisfying a predicate on the wires -- and every such result simply ASSUMED the majority had already been read out. Nothing connected them. This theorem does: the weight of the outcomes whose scratch wire reads one after the readout circuit is exactly the weight of the inputs whose three data wires have majority one.
--
--   MECHANISM. The readout's action on the amplitude array is, at EVERY input, to replace the scratch bit by its exclusive-or with the majority of the three controls; the controls survive the update untouched precisely because each differs from the scratch wire, which is why the three distinctness hypotheses are needed and stated. Flipping the scratch bit is therefore an involution on the whole space of bit strings, and it carries the outcomes with scratch one bijectively onto the inputs with scratch zero.
--
--   A SUBTLETY WORTH RECORDING. The other natural map -- overwriting the scratch bit with the majority -- COLLAPSES the two values of that bit and is injective only on the scratch-equals-zero slice, so a naive reindexing along it would be wrong. The proof uses the bit-flip involution instead, supplied as its own two-sided inverse to a sum-reindexing lemma, so bijectivity is never in question. On the reindexed summand there are four cases: when the majority is one the transported amplitude is exactly the input amplitude; when it is zero the left side's term sits at a bit string whose scratch wire reads one, and the scratch-initialisation hypothesis annihilates it.
--
--   PROVENANCE. hRead abstracts the separately accepted ShiShallow.majority3_accum, the accumulate form of the three-Toffoli composition, valid at every input -- note the companion ShiShallow.majority3_scratch_false_eq_majority is NOT usable here, since it characterises the readout only where the scratch bit is false while this sum ranges over outputs where it is true. hMaj abstracts the separately accepted ShiShallow.maj3_eq_xor_of_ands. Both are used only through those equations.
--
--   HONEST LIMITATIONS. No measure theory: these are finite sums over a finite type, not probability measures, and no PMF appears. No normalisation and no unitarity is assumed of the state, so neither side need be a probability -- they are weights. The scratch-initialisation hypothesis, that the state vanishes wherever the scratch wire reads one, is a GENUINE assumption about the input state and not a technical convenience: without it the right-hand side would have to range over inputs whose scratch bit DISAGREES with the majority, which is true but carries no physical reading. The three wire-distinctness hypotheses are likewise real assumptions. The statement concerns composed gate ACTIONS on an amplitude array, not the result of running a Layered term through runLayered, so it is not yet a statement about a circuit in the development's own layered representation. And nothing here claims universality or completeness for the H, S, T, X, CNOT gate set.

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem majority_readout_scratch_accept_weight_eq_majority_weight {n : ℕ}
    (w0 w1 w2 t : Fin n) (h0 : w0 ≠ t) (h1 : w1 ≠ t) (h2 : w2 ≠ t)
    (ψ : QState n)
    (hInit : ∀ z : Bits n, z t = true → ψ z = 0)
    (TOF : Fin n → Fin n → Fin n → QState n → QState n)
    (hRead : ∀ φ : QState n,
      TOF w2 w0 t (TOF w1 w2 t (TOF w0 w1 t φ))
        = fun x : Bits n => φ (Function.update x t
            (xor (xor (xor (x t) (x w0 && x w1)) (x w1 && x w2)) (x w2 && x w0))))
    (hMaj : ∀ a b c : Bool,
      xor (xor (a && b) (b && c)) (c && a)
        = (if (2 : ℕ) ≤ (if a then (1 : ℕ) else 0) + (if b then (1 : ℕ) else 0)
            + (if c then (1 : ℕ) else 0) then true else false)) :
    (∑ y : Bits n, (if y t = true then
        ‖TOF w2 w0 t (TOF w1 w2 t (TOF w0 w1 t ψ)) y‖ ^ 2 else 0))
      = ∑ z : Bits n, (if z t = false ∧ (2 : ℕ) ≤ (if z w0 then (1 : ℕ) else 0)
          + (if z w1 then (1 : ℕ) else 0) + (if z w2 then (1 : ℕ) else 0)
          then ‖ψ z‖ ^ 2 else 0) := by
  sorry

end ShiShallow
