-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_Supplement_theorem_6_3
-- name    : QuantumSymmetryBreaking.CycleColoring.Supplement.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:07:52.914021+00:00
-- url     : https://prove2.me/theorems/5bb993b4-24d3-42ac-8d93-473c6c60b069
-- title:
--   Theorem 6.3 — Four-round quantum-LOCAL 3-coloring of cycles and paths
-- statement:
--   For every real C≥1 and every known positive integer exponent d for the identifier range, there exists one quantum-LOCAL node-rule family A using exactly four communication rounds and three colors. For every known bound n≥1, every undirected cycle of size at least three or nonempty finite path of size m≤n, every port numbering and every injective assignment of identifiers from {0,…,n^d−1},
--
--   $$\Pr[A\text{ produces a proper 3-coloring}]\ge 1-n^{-C}.$$
--
--   Paths include their endpoints and the one-vertex path. No orientation or coloring is initially available. The initial network state is a product of locally prepared finite states, and the output law comes from four synchronous tensor-channel/register-exchange rounds and final local POVMs. This companion theorem gives the three-color palette for both graph classes.
--
--   Differences from the source:
--   - encoding: finite quantum-LOCAL operations on undirected cycles and paths → LocalAlgorithm exponent 3 4 with IsCycle ∨ IsPath; reason: finite resources are padded, and one algorithm must handle both classes; all port assignments remain quantified
--   - encoding: unique identifiers in a known polynomial range → Fin (n ^ exponent), with any positive integer exponent; reason: zero-based relabelling; a larger integer exponent covers any fixed polynomial exponent from §3
--   - encoding: known n ≥ |V| → n ≥ 1, m ≤ n, nonempty paths and cycles of length at least three; reason: only the source’s nonempty graph conventions are excluded
-- source:
--   Maxime Flin, Longcheng Li, Jukka Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), Theorem 6.3, p.29 (PDF 32)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_Supplement_LocalModel

set_option autoImplicit false

namespace QuantumSymmetryBreaking.CycleColoring.Supplement

/-- Theorem 6.3, printed p.29 (PDF 32). The exponent is any known
polynomial identifier range; node rules have no access to the global graph. -/
theorem theorem_6_3 (C : ℝ) (hC : 1 ≤ C) (exponent : ℕ) (hExponent : 1 ≤ exponent) :
    ∃ A : LocalAlgorithm exponent 3 4,
      ColorsNetworks A (fun _ G => G.IsCycle ∨ G.IsPath) C := by sorry

end QuantumSymmetryBreaking.CycleColoring.Supplement
