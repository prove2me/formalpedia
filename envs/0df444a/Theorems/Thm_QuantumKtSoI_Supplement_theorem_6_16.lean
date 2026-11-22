-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_6_16
-- name    : QuantumKtSoI.Supplement.theorem_6_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:44:30.62971+00:00
-- url     : https://prove2.me/theorems/dbef32c3-f341-4409-9d7d-7083a430a9e5
-- title:
--   Theorem 6.16, p.86 — symmetry with error $\lceil c(N+1)^\varepsilon\rceil$ puts $L_\star$ in time $2^{n^{c_P\varepsilon}}$ and outside time $t$, $\log(t+2)=o((\log(n+2))^{1/\varepsilon})$
-- statement:
--   Let $L_\star$ be a language with the properties of Theorem 2.4: computable in time $O(2^{n^{d}})$, complete for PSPACE under deterministic polynomial-time many-one reductions, downward self-reducible and random self-reducible with positive integer parameters. There is a positive integer $c_P$ such that the following holds for every constant $c\ge1$ and every rational $\varepsilon\in(0,1)$. Suppose that $\mathrm{qKt}$ satisfies symmetry of information with error $\theta(N)=\lceil c(N+1)^\varepsilon\rceil$. Then
--
--   1. some machine decides $L_\star$ in time $2^{n^{c_P\varepsilon}}$;
--   2. no machine decides $L_\star$ in time $t$, for any $t:\mathbb N\to\mathbb N$ with $\log(t(n)+2)=o\big((\log(n+2))^{1/\varepsilon}\big)$.
--
--   This ties polynomial-error symmetry of information to the quantum time complexity of PSPACE.
--
--   **Formalization Note** Deciding a language in time $t$ is the published `DecidesWithin` of the base mission (from some length on, all-branch halting, error $1/3$). The little-$o$ is: for every $\delta>0$, eventually $\log(t(n)+2)\le\delta(\log(n+2))^{1/\varepsilon}$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
--   - generalization: the one language L⋆ supplied by the cited Theorem 2.4 → every language L with the Theorem 2.4 properties (StarProps), with c_P chosen after L; reason: the paper uses only these properties of L⋆ (p.18: the reconstruction is run against one fixed language with both self-reducibility properties); L⋆ is one such language
--   - reading: an oracle procedure "writes queries and receives answers through a specified external interface" → a deterministic coded machine with a query tape and states query/yes/no, one step per oracle call; arguments of g and h encoded by the pairing; reason: the paper fixes no interface; this is one with its step counting
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 6.16, p.86; Theorem 2.4, p.19; self-reducibility, p.18

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_PSPACEHard
import Definitions.Def_QuantumKtSoI_Supplement_StarLanguage

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem 6.16** (Polynomial error and the quantum complexity of PSPACE; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.86). There is a
positive integer `c_P` such that the following holds for every constant `c ≥ 1` and every rational
`ε ∈ (0,1)`. Suppose that `qKt` satisfies symmetry of information with error
`θ(N) = ⌈c(N+1)^ε⌉`. (i) Some machine decides `L⋆` in time `2^{n^{c_P ε}}`. (ii) No machine decides
`L⋆` in time `t`, for any function `t : ℕ → ℕ` with `log(t(n)+2) = o((log(n+2))^{1/ε})`.

**Formalization Note** `L⋆` is the language supplied by the cited Theorem 2.4 (p.19); the statement
is made for every language `L` with the Theorem 2.4 properties (`StarProps`: deterministic time
`C·2^{n^d}`, PSPACE-complete under deterministic polynomial-time many-one reductions, downward and
random self-reducible), with `c_P` chosen after `L`. "Decides in time `t`" is the convention before
Theorem 4.13 for the promise problem `(L, {0,1}* ∖ L)` (the published `DecidesWithin`). The
little-o is: for every `δ > 0`, eventually `log(t(n)+2) ≤ δ (log(n+2))^{1/ε}`. Symmetry of
information with error `θ` is `Δ(x, y) ≤ θ(|x|+|y|)` for all `x, y` (Definition 5.3). `G` is any
admissible glue routine set (p.24). Logarithms are base 2. -/
theorem theorem_6_16 (G : GlueRoutines) (hG : G.Admissible) (L : Set (List Bool))
    (hL : StarProps L) :
    ∃ cP : ℕ, 0 < cP ∧ ∀ c : ℝ, 1 ≤ c → ∀ ε : ℚ, 0 < ε → ε < 1 →
      (∀ x y : List Bool,
        (defect G x y : ℝ) ≤ ⌈c * ((x.length : ℝ) + y.length + 1) ^ (ε : ℝ)⌉₊) →
      (∃ A : CodedMachine, A.Valid ∧
        DecidesWithin A L fun n => (2 : ℝ) ^ ((n : ℝ) ^ ((cP : ℝ) * ε))) ∧
      ∀ t : ℕ → ℕ,
        (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N,
          Real.logb 2 ((t n : ℝ) + 2) ≤ δ * Real.logb 2 ((n : ℝ) + 2) ^ (1 / (ε : ℝ))) →
        ¬∃ A : CodedMachine, A.Valid ∧ DecidesWithin A L fun n => (t n : ℝ) := by sorry

end QuantumKtSoI.Supplement
