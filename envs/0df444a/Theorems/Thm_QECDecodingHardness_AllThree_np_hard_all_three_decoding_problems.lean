-- Prove2me | Theorems.Thm_QECDecodingHardness_AllThree_np_hard_all_three_decoding_problems
-- name    : QECDecodingHardness.AllThree.np_hard_all_three_decoding_problems
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:50.188933+00:00
-- url     : https://prove2.me/theorems/af0b1a48-c0bf-4ea9-96e6-a0d3fcbc853e
-- title:
--   Theorem 1 — NP-hardness in all three decoding settings
-- statement:
--   Each of the following search tasks is NP-hard:
--
--   1. ColorCodeZ: given an X syndrome of a triangular hexagonal-lattice color code, find a minimum-support Z error.
--   2. SurfaceCodeXYZ: given a syndrome of a square-lattice surface code, find a minimum-support Pauli error, counting Y once.
--   3. tCNOTZ: given triggered X detectors of two square-lattice surface-code patches with 2L measurement rounds and a transversal CNOT after the first L rounds, find a minimum combined-support Z-data and measurement-bit-flip error. The end measurements are ideal.
--
--   Writing T_col, T_surf and T_CNOT for these three explicitly encoded tasks, the assertion is
--
--   $$\operatorname{NPOracleHard}(T_{\rm col})\ \land\ \operatorname{NPOracleHard}(T_{\rm surf})\ \land\ \operatorname{NPOracleHard}(T_{\rm CNOT}).$$
--
--   For each task, every polynomially verifiable language has a uniform polynomial-time oracle reduction, with actual polynomial-time Turing-machine preprocessing and postprocessing. Correctness holds for every syndrome-consistent minimizing answer. Feasible syndromes require an attained minimum error; infeasibility is reported separately. All lattice sizes are available and all syndrome inputs are allowed.
--
--   This is the complete search-hardness conclusion of Theorem 1. Gadget truth tables, correctness of a proposed 3DM reduction, preexisting target hardness, and P≠NP are not assumptions. The concrete gadget construction, matching equivalence, finite-boundary padding and polynomial computation remain proof obligations.
--
--   Differences from the source:
--   - encoding: NP-hardness of finding a minimum-weight error via the threshold decision problem → one-query oracle hardness for every published polynomially verifiable language, with TM2-computed preprocessing and postprocessing and every minimum-error output accepted; reason: p.5 obtains the search conclusion by one minimum-error call and a weight comparison; actual computation certifies uniform polynomial time
--   - encoding: finite triangular color code and square surface-code lattices with bulk padding → explicit integer-coordinate triangular patches, relative square cellulations with left/right rough boundaries, and full derived incidence tables in the query encoding; reason: fixes boundary and coordinate conventions without restricting lattice growth, syndromes or the bulk constructions; p.6 explicitly permits sufficiently large finite boundaries
--   - encoding: 2L measurement rounds with the CNOT after L rounds and ideal first/last measurements → round j at j−1/2 for j=0,...,2L−1, t_i=0, t_G=L−1, t_f=2L−2, and internal measurement faults only; reason: this time translation preserves the boxed schedule, including L=1, and the target-to-control measurement hyperedge
--   - encoding: minimum error if a syndrome-consistent error exists → explicit minimizing-error answer or a separate infeasibility flag, with totality asserted; reason: finite error sets attain feasible minima and infeasible instances are never assigned a fictitious weight zero
-- source:
--   Shouzhen (Bailey) Gu, Lily Wang, Aleksander Kubica, STOC 2027 submission #745 (October 2026), p.5, Theorem 1(1)–(3); pp.3–6, problem definitions and search/threshold link

import Definitions.Def_QECDecodingHardness_AllThree_search_hardness

namespace QECDecodingHardness.AllThree

/-- Gu–Wang–Kubica, STOC 2027 submission #745 (October 2026), p.5, Theorem 1,
all three clauses. These are the concrete lattice search tasks, with attained
minimum support, including all tie outputs. Actual polynomial-time TM2 preprocessing
and postprocessing are required by `NPOracleHard`; polynomial output size alone
is insufficient. There are no gadget, hardness, noise or P≠NP hypotheses. -/
theorem np_hard_all_three_decoding_problems :
    NPOracleHard (decodingSearchTask .colorCodeZ) ∧
    NPOracleHard (decodingSearchTask .surfaceCodeXYZ) ∧
    NPOracleHard (decodingSearchTask .transversalCNOTZ) := by sorry

end QECDecodingHardness.AllThree
