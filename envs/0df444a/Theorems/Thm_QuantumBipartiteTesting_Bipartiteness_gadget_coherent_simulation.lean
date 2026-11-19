-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_gadget_coherent_simulation
-- name    : QuantumBipartiteTesting.Bipartiteness.gadget_coherent_simulation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T13:31:45.13253+00:00
-- url     : https://prove2.me/theorems/c09d5ca4-1a5b-4172-8e78-84c7a3017014
-- title:
--   Clean coherent simulation of the gadget oracle in six queries
-- statement:
--   For every vertex count $n$, every injective null-preserving binary encoding of signed source responses, and every injective null-preserving binary encoding of gadget responses, there is an input-independent finite unitary circuit with at most six source oracle calls that simulates one query to the packed adjacency oracle of the seven-vertex path gadget.
--
--   More precisely, there is a fixed injective clean embedding $J$ of the entire logical address and answer basis into the simulation basis such that, for every consistent signed colored graph $(F,b)$ and every complex logical state $\psi$,
--
--   $$
--   U_{F,b}J\psi=J O_{G(F,b)}\psi.
--   $$
--
--   Here $O_{G(F,b)}$ is the encoded XOR oracle for the sorted packed neighbor list of the gadget, and $U_{F,b}$ consists of input-independent unitary gates interleaved with at most six encoded signed-source XOR queries. The equality includes every answer-register bit string, dummy addresses, arbitrary superpositions, and a clean return of the auxiliary registers.
--
--   This makes the constant-query coherent simulation in Lemma 3.16 explicit. Three source response registers are computed and then cleared by three further source calls.
-- source:
--   Kayal, Sen, Szabó, held October 2026 manuscript, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, §3.6 pp.20–21, Lemma 3.16, final proof paragraph on reversible coherent simulation. The explicit constant six counts three response queries and their three inverse queries.

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

theorem QuantumBipartiteTesting.Bipartiteness.gadget_coherent_simulation : QuantumBipartiteTesting.Bipartiteness.CoherentSimulation 6 := by sorry
