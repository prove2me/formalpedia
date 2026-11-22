-- Prove2me | Theorems.Thm_StabilizerRank_stabRank_hState_six_le_seven
-- name    : StabilizerRank.stabRank_hState_six_le_seven
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-07T22:03:14.134208+00:00
-- url     : https://prove2.me/theorems/8e1caf28-0624-4224-a918-bba20e47ebbb
-- title:
--   Bravyi--Smith--Smolin: $\chi(|H^{\otimes 6}\rangle)\le 7$
-- statement:
--   The six-fold tensor power of the magic state admits a decomposition into only seven stabilizer states:
--
--   $$\chi\bigl(|H^{\otimes 6}\rangle\bigr)\;\le\;7 .$$
--
--   The trivial bound for six qubits is $2^6=64$, so this is a substantial saving, and it is the source of the best known asymptotic upper bound: applying it blockwise to $6k$ qubits gives $\chi(|H^{\otimes n}\rangle)\le 7^{\,n/6}\le 2^{\,0.468\,n}$, which is what makes stabilizer-rank simulation of Clifford-plus-magic-state circuits competitive in practice.
--
--   The statement is finite and fully explicit: establishing it amounts to exhibiting seven stabilizer states of six qubits and seven complex coefficients, then verifying $2^6=64$ coordinate identities. It therefore requires no asymptotic analysis, only a concrete witness.
-- source:
--   S. Peleg, A. Shpilka, B. L. Volk, Lower Bounds on Stabilizer Rank, Quantum 6 (2022) 652; arXiv:2106.03214, p. 2: "Bravyi, Smith and Smolin [7] proved that chi(H^{ox 6}) <= 7 which implies that chi(H^{ox n}) <= 7^{n/6} <= 2^{0.468n}". Cited there as reference [7]; the bound is due to Bravyi, Smith and Smolin, and is quoted here from Peleg-Shpilka-Volk rather than from the original paper.

import Definitions.Def_StabilizerRank

namespace StabilizerRank

theorem stabRank_hState_six_le_seven : stabRank (hState 6) ≤ 7 := by sorry

end StabilizerRank
