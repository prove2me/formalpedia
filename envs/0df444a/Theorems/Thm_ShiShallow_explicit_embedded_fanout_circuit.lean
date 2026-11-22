-- Prove2me | Theorems.Thm_ShiShallow_explicit_embedded_fanout_circuit
-- name    : ShiShallow.explicit_embedded_fanout_circuit
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-18T11:26:58.822973+00:00
-- url     : https://prove2.me/theorems/5f1d78ac-f0f7-44b7-acb6-999f4c6fc728
-- title:
--   The embedded fan-out as a literal one-layer circuit
-- statement:
--   A fan-out embedded along an injection is available only up to its action, which leaves its gate list undetermined and so leaves the encoding of any circuit built from it undetermined too. Here the circuit is pinned as a term: a single layer holding one controlled-not per wire of the source register, from the image of the low half to the image of the high half, with the two wires' distinctness supplied inline from injectivity. The permutation of basis strings it induces is pinned as well, the relevant source wire being unique by injectivity. Layerwise well-formedness needs the gates' supports to be pairwise disjoint, and injectivity of the embedding alone suffices: the low-half and high-half images have disjoint ranges before embedding, and the embedding transports that. A non-identity embedding is exhibited with its literal gate list, its depth, and the induced action on a concrete basis string, including a wire outside the embedding's high-half range that is left unchanged.

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

open ShiShallow

namespace ShiShallow

theorem explicit_embedded_fanout_circuit :
    (∀ (n N : ℕ) (g : Fin (n + n) → Fin N) (hg : Function.Injective g),
      ∃ (c : Layered N) (u : Bits N → Bits N),
        c = [(List.finRange n).map (fun j : Fin n =>
              Instr.cnot (g (Fin.castAdd n j)) (g (Fin.natAdd n j))
                (fun h => by
                  have hj : (j : ℕ) < n := j.isLt
                  have hv : (j : ℕ) = n + (j : ℕ) := congrArg Fin.val (hg h)
                  omega))]
        ∧ u = (fun (x : Bits N) (k : Fin N) =>
              if h : ∃ j : Fin n, g (Fin.natAdd n j) = k
                then xor (x k) (x (g (Fin.castAdd n h.choose))) else x k)
        ∧ (∀ Φ : QState N, runLayered c Φ = fun Y => Φ (u Y))
        ∧ (∀ (Y : Bits N) (j : Fin n), u Y (g (Fin.natAdd n j))
              = xor (Y (g (Fin.natAdd n j))) (Y (g (Fin.castAdd n j))))
        ∧ (∀ (Y : Bits N) (k : Fin N), (∀ j : Fin n, g (Fin.natAdd n j) ≠ k) → u Y k = Y k)
        ∧ (∀ l ∈ c, LayerOk l)
        ∧ depth c = 1)
    ∧ (∃ (c : Layered 6) (u : Bits 6 → Bits 6),
        c = [[Instr.cnot (⟨1, by omega⟩ : Fin 6) ⟨3, by omega⟩ (by decide),
              Instr.cnot (⟨2, by omega⟩ : Fin 6) ⟨4, by omega⟩ (by decide)]]
        ∧ (∀ Φ : QState 6, runLayered c Φ = fun Y => Φ (u Y))
        ∧ (∀ l ∈ c, LayerOk l)
        ∧ depth c = 1
        ∧ u (fun k => decide ((k : ℕ) = 1 ∨ (k : ℕ) = 5)) ⟨3, by omega⟩ = true
        ∧ u (fun k => decide ((k : ℕ) = 1 ∨ (k : ℕ) = 5)) ⟨4, by omega⟩ = false
        ∧ u (fun k => decide ((k : ℕ) = 1 ∨ (k : ℕ) = 5)) ⟨0, by omega⟩ = false
        ∧ u (fun k => decide ((k : ℕ) = 1 ∨ (k : ℕ) = 5)) ⟨5, by omega⟩ = true) := by
  sorry

end ShiShallow
