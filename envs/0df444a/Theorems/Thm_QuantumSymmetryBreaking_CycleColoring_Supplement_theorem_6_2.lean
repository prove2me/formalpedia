-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_Supplement_theorem_6_2
-- name    : QuantumSymmetryBreaking.CycleColoring.Supplement.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:07:22.519033+00:00
-- url     : https://prove2.me/theorems/f5f10f6c-cc10-42eb-b9e9-421801af19b6
-- title:
--   Theorem 6.2 — One-round quantum-LOCAL coloring of undirected cycles
-- statement:
--   For every real C≥1 and every known positive integer exponent d for the polynomial identifier range, there exists a single quantum-LOCAL node-rule family A. It uses exactly one communication round and exactly 20002 colors. For every known bound n≥1, every undirected cycle with 3≤m≤n vertices, every port numbering and every injective assignment of identifiers from {0,…,n^d−1}, the operational Born law satisfies
--
--   $$\Pr[A\text{ produces a proper coloring}]\ge 1-n^{-C}.$$
--
--   No consistent orientation or initial coloring is supplied. Registers start in a product state across nodes. Local resources may depend on n. The guarantee is global and uniform over the adversarial network and identifier choices. This companion theorem removes the directed-orientation assumption.
--
--   Differences from the source:
--   - encoding: finite quantum-LOCAL operations on arbitrary port-numbered cycles → LocalAlgorithm exponent 20002 1 and ColorsNetworks over PortNetwork.IsCycle; reason: finite registers are padded; the imported Kraus channel covers arbitrary local operations and the tensor/permutation evolution is literal
--   - encoding: unique identifiers in a known polynomial range → Fin (n ^ exponent), with any positive integer exponent; reason: zero-based relabelling; a larger integer exponent covers any fixed polynomial exponent from §3
--   - encoding: known n ≥ |V| → n ≥ 1 and m ≤ n, with m ≥ 3 in IsCycle; reason: nonempty cycles already imply a positive bound
-- source:
--   Maxime Flin, Longcheng Li, Jukka Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), Theorem 6.2, p.29 (PDF 32)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_Supplement_LocalModel

set_option autoImplicit false

namespace QuantumSymmetryBreaking.CycleColoring.Supplement

/-- Theorem 6.2, printed p.29 (PDF 32). The exponent is any known
polynomial identifier range; node rules have no access to the global graph. -/
theorem theorem_6_2 (C : ℝ) (hC : 1 ≤ C) (exponent : ℕ) (hExponent : 1 ≤ exponent) :
    ∃ A : LocalAlgorithm exponent 20002 1,
      ColorsNetworks A (fun _ G => G.IsCycle) C := by sorry

end QuantumSymmetryBreaking.CycleColoring.Supplement
