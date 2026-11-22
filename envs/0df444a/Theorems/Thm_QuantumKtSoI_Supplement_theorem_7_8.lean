-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_7_8
-- name    : QuantumKtSoI.Supplement.theorem_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:45:45.099802+00:00
-- url     : https://prove2.me/theorems/b931a097-ae30-407c-893d-ebe3210c4bd2
-- title:
--   Theorem 7.8, p.107 — no native machine decides $\mathrm{Gap\text{-}MqKtP}[\lfloor N^\gamma\rfloor,N-2]$ in time $O(2^{N^{\delta}})$ and charged space $O(N^\varsigma)$
-- statement:
--   For every rational $\gamma\in(0,1)$ and integer $\varsigma\ge1$ there is a rational $\delta_{\varsigma,\gamma}>0$ with the following property. No native quantum machine decides $\mathrm{Gap\text{-}MqKtP}[\lfloor N^\gamma\rfloor,N-2]$ in all-branch time $O(2^{N^{\delta_{\varsigma,\gamma}}})$ and charged space $O(N^\varsigma)$ at all sufficiently large lengths. Correctness is required only on the two promise sets.
--
--   The charged space of a branch (Definition 7.6) is
--   $$\mathrm{sp}_A(x,\rho)=|x|+\sum_{j\ne\mathrm{in}}(v_j+1)\lceil\log(|\Sigma_j|+1)\rceil+\sum_j\lceil\log(h_j+2)\rceil+\lceil\log(|Q_A|+2)\rceil .$$
--
--   This is the gap lower bound at an exponential time bound for machines of polynomial charged space.
--
--   **Formalization Note** The gap problem uses the clipped thresholds of p.49.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
--   - reading: time O(2^{N^δ}) and charged space O(N^ς) in the hypothesis of a negative statement → for all real constants C₁, C₂: no machine with time C₁·2^{N^δ} and charged space C₂·N^ς; reason: p.49 and p.105: O(T) means CT for a constant C; excluding O(·) excludes every constant
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 7.8, p.107; Definition 7.6, p.105

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_DecidesPromise
import Definitions.Def_QuantumKtSoI_Supplement_GapMqKtP
import Definitions.Def_QuantumKtSoI_Supplement_chargedSpace

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem 7.8** (Space-restricted gap lower bound; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.107). For every rational
`γ ∈ (0,1)` and integer `ς ≥ 1`, there is a rational `δ_{ς,γ} > 0` such that no native quantum
machine decides `Gap-MqKtP[⌊N^γ⌋, N − 2]` in all-branch time `O(2^{N^{δ_{ς,γ}}})` and charged space
`O(N^ς)` at all sufficiently large lengths. Correctness is required only on the two promise sets.

**Formalization Note** The two `O(·)` bounds sit in the hypothesis of a negative statement, so the
statement excludes them for all constants `C₁, C₂`. Gap-MqKtP uses the clipped thresholds of p.49;
"decides in time" is the convention of p.49 (`DecidesPromise`); charged space is Definition 7.6
(`RunsInChargedSpace`). A native machine is a valid coded machine. `G` is any admissible glue
routine set (p.24). -/
theorem theorem_7_8 (G : GlueRoutines) (hG : G.Admissible) :
    ∀ γ : ℚ, 0 < γ → γ < 1 → ∀ ς : ℕ, 1 ≤ ς → ∃ δ : ℚ, 0 < δ ∧ ∀ C₁ C₂ : ℝ,
      ¬∃ A : CodedMachine, A.Valid ∧
        DecidesPromise A
          (GapMqKtPClip (fun x => (qKt G x [] : ℝ)) fun N => ⌊(N : ℝ) ^ (γ : ℝ)⌋₊).1
          (GapMqKtPClip (fun x => (qKt G x [] : ℝ)) fun N => ⌊(N : ℝ) ^ (γ : ℝ)⌋₊).2
          (fun N => C₁ * (2 : ℝ) ^ ((N : ℝ) ^ (δ : ℝ))) ∧
        RunsInChargedSpace A.toMachine fun N => C₂ * (N : ℝ) ^ ς := by sorry

end QuantumKtSoI.Supplement
