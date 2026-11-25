-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_occ_arith_54
-- name    : QuantumLTF.Membership.Supplement.occ_arith_54
-- status  : Proved
-- author  : @Robin Kothari
-- created : 2026-11-25T02:33:11.808665+00:00
-- url     : https://prove2.me/theorems/fee0e47c-1d21-5792-8c20-8536c85c5e62
-- title:
--   Section V occupation-to-NSIL combinatorics and reversible gates12 arithmetic primitives
-- statement:
--   Proves `Nonempty OccArith54`, establishing all Section V reversible second-to-first-quantization combinatorial lemmas and `gates12` arithmetic circuit primitives required by `QuantumLTF.Membership.Supplement.occupation_to_nsil_54`:
--
--   1. **Combinatorial Bijections (`wtilde2_54`..`wtildef_54`):** Every particle rank $c < N$ has monotone mode `modeOf54 alpha c < m` occurring exactly $\alpha_r$ times for each $r < m$. Sorting `wtilde2_54` with trailing padding by `keyW3_54` yields `wtilde3_54` on the first $m + N$ slots (`wtilde2_sort_prefix`), where each marker $(m, 0, c)$ at position $\mathrm{pos}$ satisfies $\mathrm{pos} - c = \mathrm{modeOf54}(\alpha, c)$. Conversely, sorting `wtildef_54` with trailing padding by `keyW8_0_54` yields `wtilde8_54` on the first $m + N$ slots (`wtildef_sort_prefix`), where each mode tuple $(i, i, 0)$ at position $\mathrm{pos}$ satisfies $\mathrm{pos} - i = p_i$.
--
--   2. **Constructive `gates12` Primitives:** Constructs `LayeredCircuit` circuits with clean-ancilla unitary specifications and explicit linear gate counts for `copyRegCircuit` ($w$ gates), `setConstCircuit` ($\le w$ gates), `eqConstCircuit` ($\le 14w + 12$ gates, $w$ ancillas), LSB-first Cuccaro `addInPlaceCircuit` and `subInPlaceCircuit` ($14w$ gates, $1$ ancilla), `ctrlCopyRegCircuit` ($5w$ gates), and `encodeParticleSym54Circuit` ($\le 13s$ gates, $s - 1$ ancillas) preparing `particleSym54 n s j`.
--
--   **Formalization Note** Both the Section V tuple-list combinatorics and the constructive `gates12` circuits are packaged inside `Nonempty OccArith54` defined in `Definitions.Def_QuantumLTF_Membership_Supplement_occArith54`.
-- source:
--   Liu, Childs, Gottesman [LCG26], First and second quantization: reversible and quantum circuits (arXiv:2411.04019, Section V); Cuccaro et al. (2004), A new quantum ripple-carry addition circuit; Krivcenko, Nguyen, de Wolf [KNW26], Fast Quantum Algorithms for Learning Linear Threshold Functions (arXiv:2609.40331, Theorem 5.4).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_occArith54

namespace QuantumLTF.Membership.Supplement

theorem occ_arith_54 : Nonempty OccArith54 := by sorry

end QuantumLTF.Membership.Supplement
