-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_F_9
-- name    : QuantumKtSoI.Supplement.theorem_F_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:00:06.867636+00:00
-- url     : https://prove2.me/theorems/ed633ac6-3ec2-4199-9a88-a8e45da033f5
-- title:
--   Theorem F.9, p.244 — the symmetry failures hold for the padded universal machine of Lemma F.7
-- statement:
--   Let $U$ be the machine of Lemma F.7: a machine with integers $k\ge2$ and $c_U\ge1$ such that for all strings $p,y,w$: (i) if $p$ is not a description, $P_U(\langle p,y\rangle;t,w)=0$ for every $t\ge1$; (ii) if $p$ is a description, $P_U(\langle p,y\rangle;c_U(|p|+|y|+s+2)^k,w)\ge P_p(y;s,w)$ for every $s\ge0$; (iii) if $p$ is a description, $P_U(\langle p,y\rangle;t,w)\le P_p(y;\lfloor(kt)^{1/k}\rfloor,w)$ for every $t\ge1$.
--
--   Then Theorems 5.10, 5.16 and 5.22 and Corollary 5.13 hold with $\mathrm{qKt}_U$ in place of $\mathrm{qKt}$, with the same scales and the same polynomial $p(n)=8000n^2$. In particular, both the worst-case and average-case failures hold for this machine, which satisfies Equation (23) with $d_U=k\ge2$.
--
--   This is an explicit polynomially universal machine with a genuinely polynomial simulation exponent for which the symmetry failures survive.
--
--   **Formalization Note** Each restated result is the measure-parameterized statement of the module `SoIFailures`.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
--   - generalization: U is the one machine constructed in Lemma F.7 → a machine with properties (i)–(iii) of Lemma F.7 exists, and every such machine (with its k, c_U) has the conclusion; reason: the proof (pp.244–245) uses only (i)–(iii), through Lemma F.8 and the last assertion of Lemma F.7; the paper's machine is one of them
--   - encoding: qKt_U, with the minimum of the empty set equal to +∞ → qKt_U is ℕ∞-valued; the statement first asserts that it is finite everywhere and then reads its values as reals; reason: the restated results are inequalities between finite values; finiteness holds for every polynomially universal machine (p.118)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem F.9, p.244; Lemma F.7, p.242; Equation (23), p.118

import Mathlib
import Definitions.Def_QuantumKtSoI_Supplement_qKtU
import Definitions.Def_QuantumKtSoI_Supplement_SoIFailures

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem F.9** (The symmetry failures for a universal machine; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.244). Let `U` be the
machine of Lemma F.7. Then Theorems 5.10, 5.16 and 5.22 and Corollary 5.13 hold with `qKt_U` in
place of `qKt`, with the same scales and the same polynomial `p(n) = 8000n²`. In particular, both
the worst-case and average-case failures hold for this machine, which satisfies Equation (23) with
`d_U = k ≥ 2`.

**Formalization Note** "The machine of Lemma F.7" is read as any machine `U` with integers
`k ≥ 2`, `c_U ≥ 1` satisfying Lemma F.7 (i)–(iii) (`PaddedUniversal`); the statement asserts that
such a machine exists and that every one of them has the conclusion (the proof on pp.244–245 uses
only (i)–(iii)). `qKt_U` is `ℕ∞`-valued (p.117); its finiteness is asserted first and its values are
then read in `ℝ`. The restated results are `Thm510For`, `Cor513For`, `Thm516For`, `Thm522For`
(module `SoIFailures`), and Equation (23) is `PolyUniversal` with positive `k_U, C_U` and
`d_U = k`. `G` is any admissible glue routine set (p.24). -/
theorem theorem_F_9 (G : GlueRoutines) (hG : G.Admissible) :
    (∃ U : CodedMachine, ∃ k cU : ℕ, PaddedUniversal G U k cU) ∧
    ∀ U : CodedMachine, ∀ k cU : ℕ, PaddedUniversal G U k cU →
      (∀ y x : List Bool, qKtU U y x ≠ ⊤) ∧
      Thm510For (fun y x => ((qKtU U y x).toNat : ℝ)) ∧
      Cor513For (fun y x => ((qKtU U y x).toNat : ℝ)) ∧
      Thm516For (fun y x => ((qKtU U y x).toNat : ℝ)) ∧
      Thm522For (fun y x => ((qKtU U y x).toNat : ℝ)) ∧
      ∃ kU CU : ℕ, 0 < kU ∧ 0 < CU ∧ PolyUniversal G U kU CU k := by sorry

end QuantumKtSoI.Supplement
