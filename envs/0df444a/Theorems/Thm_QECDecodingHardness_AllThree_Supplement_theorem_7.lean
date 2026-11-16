-- Prove2me | Theorems.Thm_QECDecodingHardness_AllThree_Supplement_theorem_7
-- name    : QECDecodingHardness.AllThree.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:47:30.750417+00:00
-- url     : https://prove2.me/theorems/4f8fa2c7-6d33-4e13-93bf-d7888634255e
-- title:
--   Theorem 7 — NP-hardness of deciding the logical effect of a minimum-weight error
-- statement:
--   In each of the three decoding scenarios of the mission — ColorCodeZ (triangular color code, $Z$ errors, $X$ syndrome), SurfaceCodeXYZ (square-lattice surface code, Pauli errors, support weight with $Y$ counted once) and tCNOTZ (two surface-code patches with a transversal CNOT, $Z$ data and measurement bit-flip faults) — consider the decision problem: given the code's size parameter, a syndrome $\sigma$, and a representative $P$ of a logical operator of the code, decide whether some minimum-weight error $E$ with syndrome $\sigma$ anticommutes with $P$, i.e.
--
--   $$\exists E\ \text{minimum-weight with syndrome } \sigma:\quad \langle \mathrm{eff}(E), P\rangle = 1 .$$
--
--   Here $\langle\cdot,\cdot\rangle$ is the binary symplectic product and $\mathrm{eff}(E)$ is $E$ itself in the two code-capacity settings and the end-of-circuit propagated $Z$ frame of $E$ in tCNOTZ. Writing $T^{\log}_{\rm col}$, $T^{\log}_{\rm surf}$, $T^{\log}_{\rm CNOT}$ for the three encoded one-bit tasks, the theorem asserts
--
--   $$\operatorname{NPOracleHard}(T^{\log}_{\rm col})\ \land\ \operatorname{NPOracleHard}(T^{\log}_{\rm surf})\ \land\ \operatorname{NPOracleHard}(T^{\log}_{\rm CNOT}).$$
--
--   That is, for every polynomially verifiable language there is a polynomial-time Turing-machine preprocessing producing one query and a polynomial-time postprocessing of the input and the oracle's bit that decides membership. Every lattice size, every syndrome and every logical representative (of any Pauli type and shape) is an admissible query.
--
--   The result shows that even the logical effect of a minimum-weight correction — the only information needed to recover the encoded state — is hard to determine, so the hardness of Theorem 1 is not an artifact of asking for the full error.
--
--   Differences from the source:
--   - encoding: "NP-hard" for a decision problem → `NPOracleHard` of the one-bit task (one oracle query, TM2 polynomial-time preprocessing and postprocessing, the postprocessing may negate the bit); reason: this is the paper's own p.5 meaning ("if we can solve A, then we can solve any NP problem with polynomial time overhead") and the base mission's hardness notion
--   - reading: "deciding if a minimum-weight error anticommutes with P" → some minimum-weight error with the given syndrome anticommutes with P (false on infeasible syndromes); reason: the literal existential reading, which is the one the proof on pp.17–19 establishes; the reading "every minimum-weight error anticommutes" is not established by the proof
--   - reading: "anticommutes with a given representative of a logical operator" in tCNOTZ → symplectic product of P (a logical of the two-patch code at the end of the circuit) with the error's Z frame propagated through the transversal CNOT (patch-2 Z faults before t_G copied to patch 1, measurement faults ignored); reason: the paper does not spell out the spacetime meaning; this is the standard logical observable of the circuit
--   - encoding: representative of a logical operator → Pauli modulo phase commuting (symplectic product 0) with every X and Z generator of the code and outside the F₂-span of the generators; the color code's Z vertex checks are added from the base coordinates; reason: the standard definition of a nontrivial logical operator of a stabilizer code (p.3); no instance is changed
--   - encoding: lattices and schedule → the base mission's published patches (color code of order k, L×L surface patch with L = k+1, t_G = L−1, data faults at t_G after the gate) and the base nonsuccinct instance encoding followed by the 2·(number of qubits) bits of P; reason: inherited from the published base model; all lattice sizes remain queries
-- source:
--   Shouzhen (Bailey) Gu, Lily Wang, Aleksander Kubica, STOC 2027 submission #745 (October 2026), p.17, Theorem 7 (proof pp.17–19, Fig. 12 p.18); setting pp.3–5

import Definitions.Def_QECDecodingHardness_AllThree_Supplement_logical_operators

namespace QECDecodingHardness.AllThree.Supplement

/-- Gu–Wang–Kubica, STOC 2027 submission #745 (October 2026), p.17, Theorem 7, all
three scenarios. Deciding whether some minimum-weight error anticommutes with a given
logical representative is NP-hard (`NPOracleHard` of the one-bit task, the base
mission's hardness notion). Every lattice size, syndrome and logical representative
is an admissible query. -/
theorem theorem_7 :
    NPOracleHard colorLogicalTask ∧
    NPOracleHard surfaceLogicalTask ∧
    NPOracleHard cnotLogicalTask := by sorry

end QECDecodingHardness.AllThree.Supplement
