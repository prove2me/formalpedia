-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_theorem_1_1
-- name    : SignFreeOracle.Separation.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:11.184795+00:00
-- url     : https://prove2.me/theorems/2578f9d4-ab4b-4dff-b5a0-00f37a94a3d1
-- title:
--   Theorem 1.1 — one classical oracle strictly separates MA from StoqMA
-- statement:
--   There exists one total Boolean oracle $O:\{0,1\}^*\to\{0,1\}$ such that the operational relativized promise-problem classes satisfy
--   $$\mathrm{MA}^O\subsetneq\mathrm{StoqMA}^O.$$
--   Thus every promise problem with a probabilistic polynomial-time classical oracle verifier and polynomial classical witnesses has a restricted uniform stoquastic verifier, and some promise problem has the latter verification but no former verification, relative to the same fixed oracle. StoqMA soundness quantifies over all normalized complex witnesses. MA quantifies over all finite polynomially clocked randomized machines, without a quadratic-time restriction or nonuniform advice. The oracle acts by Boolean XOR queries; its encoding counts the work to write the entire address. This is the full-strength main theorem on p. 17, rather than only a graph-query lower bound.
--
--   Differences from the source:
--   - encoding: MA and StoqMA with classical oracle access → finite polynomial clocks, fair-coin strings, prefix-coded restricted circuits, arbitrary complex witnesses and one Boolean string oracle; reason: these implement Definitions 2.1–2.2, with equivalent input and output-wire conventions and no advice
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Theorem 1.1, p. 17 (PDF p. 17); introductory form p. 2 (PDF p. 2)

import Definitions.Def_SignFreeOracle_Separation_MA
import Definitions.Def_SignFreeOracle_Separation_StoqMA

set_option autoImplicit false

namespace SignFreeOracle.Separation

/-- Hamoudi, Le Borgne and Teganahally Sridhara, STOC 2027 submission #601,
October 2026, Theorem 1.1, p. 17 (also p. 2). The same total Boolean oracle
strictly separates the operational promise-problem classes of Definitions 2.1–2.2. -/
theorem theorem_1_1 : ∃ O : QAdvFew.PoQOracle.Oracle, MA O ⊂ StoqMA O := by sorry

end SignFreeOracle.Separation
