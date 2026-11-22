-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_4_13
-- name    : QuantumKtSoI.Supplement.theorem_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:41:07.714773+00:00
-- url     : https://prove2.me/theorems/106e5dbc-52b0-425a-b90d-981595747c87
-- title:
--   Theorem 4.13, p.50 — no machine decides $\mathrm{Gap\text{-}MqKtP}[c,N-2]$ in time $H_a(N)$, nor in time $2^{(\log N)^b}$
-- statement:
--   Let $a\ge1$ be an integer and $\gamma\in(0,1)$, and let $c:\mathbb N\to\mathbb N$ satisfy $\lfloor N^\gamma\rfloor\le c(N)\le N-2$ for all large $N$. Write $\mathrm{Gap\text{-}MqKtP}[c,N-2]$ for the promise problem with
--   $$\mathrm{YES}_N=\{x\in\{0,1\}^N:\mathrm{qKt}(x)\le c_{\mathrm{clip}}(N)\},\qquad\mathrm{NO}_N=\{x\in\{0,1\}^N:\mathrm{qKt}(x)>s_{\mathrm{clip}}(N)\},$$
--   where $s_{\mathrm{clip}}(N)=\max(N-2,0)$ and $c_{\mathrm{clip}}(N)=\min(c(N),s_{\mathrm{clip}}(N))$, and let $H_a(N)=2^{2^{\Lambda_2(N)^a}}$ with $\Lambda_2(N)=\lceil\log\lceil\log(N+4)\rceil\rceil$.
--
--   1. No machine decides $\mathrm{Gap\text{-}MqKtP}[c,N-2]$ in time $H_a(N)$.
--   2. Consequently, for every fixed real $b\ge1$, no machine decides it in time $2^{(\log N)^b}$.
--
--   A machine decides a promise problem in time $T$ if, from some length on, it halts within $T(n)$ steps on every branch, accepts YES instances with probability at least $2/3$ and NO instances with probability at most $1/3$.
--
--   This is the unconditional lower bound for minimizing quantum Kt complexity beyond every quasipolynomial time bound; it is the engine of the worst-case symmetry failure.
--
--   **Formalization Note** $\mathrm{qKt}$ is the published measure of the base mission, read in $\mathbb R$; logarithms are base $2$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 4.13, p.50; Definition 4.12 and conventions, p.49; clocks, p.48

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_Ha
import Definitions.Def_QuantumKtSoI_Supplement_DecidesPromise
import Definitions.Def_QuantumKtSoI_Supplement_GapMqKtP

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem 4.13** (Gap minimization lower bound; restatement of Theorem 1.6; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.50). Let
`a ≥ 1` be an integer and `γ ∈ (0,1)`. Let `c : ℕ → ℕ` satisfy `⌊N^γ⌋ ≤ c(N) ≤ N − 2` for all
large `N`. No machine decides `Gap-MqKtP[c, N − 2]` in time `H_a(N)`. Consequently, for every fixed
real `b ≥ 1`, no machine decides `Gap-MqKtP[c, N − 2]` in time `2^{(log N)^b}`.

**Formalization Note** The glue routines `G` are any admissible set (p.24), as in the base mission.
`Gap-MqKtP[c, N − 2]` uses the clipped thresholds of p.49 (`GapMqKtPClip`); "decides in time `T`"
is the convention of p.49 (`DecidesPromise`: all-branch halting by `⌊T(n)⌋`, from some length on);
a machine is a valid coded machine. Logarithms are base 2. -/
theorem theorem_4_13 (G : GlueRoutines) (hG : G.Admissible) (a : ℕ) (ha : 1 ≤ a) (γ : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (c : ℕ → ℕ)
    (hc : ∃ N₀ : ℕ, ∀ N ≥ N₀, ⌊(N : ℝ) ^ γ⌋₊ ≤ c N ∧ c N ≤ N - 2) :
    (¬∃ B : CodedMachine, B.Valid ∧
      DecidesPromise B (GapMqKtPClip (fun x => (qKt G x [] : ℝ)) c).1
        (GapMqKtPClip (fun x => (qKt G x [] : ℝ)) c).2 (fun N => (Ha a N : ℝ))) ∧
    ∀ b : ℝ, 1 ≤ b → ¬∃ B : CodedMachine, B.Valid ∧
      DecidesPromise B (GapMqKtPClip (fun x => (qKt G x [] : ℝ)) c).1
        (GapMqKtPClip (fun x => (qKt G x [] : ℝ)) c).2
        (fun N => (2 : ℝ) ^ (Real.logb 2 (N : ℝ)) ^ b) := by sorry

end QuantumKtSoI.Supplement
