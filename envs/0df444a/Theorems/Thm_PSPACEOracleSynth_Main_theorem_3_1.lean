-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_theorem_3_1
-- name    : PSPACEOracleSynth.Main.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:35.525324+00:00
-- url     : https://prove2.me/theorems/74910611-b766-49b0-9521-069f087ba052
-- title:
--   Theorem 3.1 — one polynomial-time algorithm implements every unitary with polynomial-space entries, given a $\mathsf{PSPACE}^A$ oracle $B$
-- statement:
--   Let $A$ be a classical oracle and let $\mathcal U$ be a unitary language with entries computable in polynomial space relative to $A$ (Definition 2.4). There are a language $B\in\mathsf{PSPACE}^A$ and a polynomial-time algorithm that maps $(1^n,1^m)$ to a unitary circuit $C_{n,m}$ over $G$ such that, for all $n,m\ge1$, some extension $\tilde U$ of $U_n$ satisfies
--   $$\|C^B_{n,m}-\tilde U\|\le2^{-m}.$$
--   The algorithm that produces $C_{n,m}$ is the same for every $A$ and every $\mathcal U$, and only $B$ depends on them.
--
--   This is the main technical result: it gives the inclusion $\mathsf{unitaryPSPACE}^A\subseteq\bigcup_{L\in\mathsf{PSPACE}^A}\mathsf{unitaryP}^L$ of Theorem 1.1 (through Fact 2.5), and with the entry oracle of an arbitrary unitary language it answers the Unitary Synthesis Problem (Corollary 1.2).
--
--   **Formalization Note.** The quantifier order carries the last sentence: the encoding $f$ (with an FPTEAS), the circuits $C_{n,m}$ and their polynomial-time generator (`TimeUniform` on input `tup [1^n, 1^m]`) are chosen before $A$ and $\mathcal U$, and only $B$ after them. $C^B_{n,m}$ is the circuit with its oracle gates set to $O_B$ (the unitary embedding `emb` of $B$). The extension has the data on the first $n$ wires.
--
--   Differences from the source:
--   - encoding: a polynomial-time algorithm mapping (1^n, 1^m) to C_{n,m}, n, m ≥ 1 → a TimeUniform family indexed by all (n, m) ∈ ℕ², the conditions asked for n, m ≥ 1; reason: the outputs at n = 0 or m = 0 are unconstrained, as in the source
--   - encoding: unitary circuit over G → a published UCircuit whose explicit gates decode under one FPTEAS encoding f exactly to H, T, T†, CNOT and whose oracle gates are plain O_m; reason: the circuit model of [KT26] adopted on p. 9
--   - encoding: classical oracle A ⊆ {0,1}*, language K → A : Str → Bool; K : Set Str used through langOracle K and the unitary embedding emb; reason: Lean convention; same oracles
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §3, Theorem 3.1, p. 15 (proof pp. 27–28)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QAdvFew_PoQOracle_PSPACE
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_HasFPTEAS
import Definitions.Def_KTUnitary_Synth_UCircuit
import Definitions.Def_KTUnitary_Synth_IsExtension
import Definitions.Def_KTUnitary_Synth_opNorm
import Definitions.Def_KTUnitary_Synth_TimeUniform
import Definitions.Def_PSPACEOracleSynth_Main_Oracles
import Definitions.Def_PSPACEOracleSynth_Main_GateSet

open QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth

namespace PSPACEOracleSynth.Main

/-- **Theorem 3.1**, Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission
#1740, p. 15 (proof pp. 27–28). Let `A` be a classical oracle and let `U` be a unitary language with
entries computable in polynomial space relative to `A`. There are a language `B ∈ PSPACE^A` and a
polynomial-time algorithm that maps `(1^n, 1^m)` to a unitary circuit `C_{n,m}` over `G` such that,
for all `n, m ≥ 1`, some extension `Ũ` of `U_n` satisfies `‖C^B_{n,m} − Ũ‖ ≤ 2^{−m}`. The algorithm
that produces `C_{n,m}` is the same for every `A` and every `U`, and only `B` depends on them.

The encoding `f`, the circuits `C n m` and their polynomial-time generator are chosen before `A`
and `U`; only `B` is chosen after them. -/
theorem theorem_3_1 :
    ∃ (f : Str → ℝ) (C : ℕ → ℕ → UCircuit), HasFPTEAS f ∧
      TimeUniform (fun nm : ℕ × ℕ => tup [unary nm.1, unary nm.2]) (fun nm => (C nm.1 nm.2).code) ∧
      (∀ n m : ℕ, 1 ≤ n → 1 ≤ m → OverG f (C n m)) ∧
      ∀ (A : Oracle) (U : ULang), HasPSpaceEntries A U →
        ∃ B ∈ PSPACE A, ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
          ∃ h : n ≤ (C n m).N, ∃ Ub, IsExtension h (U n : Matrix (Bits n) (Bits n) ℂ) Ub ∧
            opNorm ((C n m).unitary f (emb (langOracle B)) - Ub) ≤ (2 : ℝ)⁻¹ ^ m := by sorry

end PSPACEOracleSynth.Main
