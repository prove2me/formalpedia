-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P05_noLowEnergyTrivialStates
-- name    : QAlgorithms.Papers.Independent.Independent1.P05.noLowEnergyTrivialStates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:41:48.829903+00:00
-- url     : https://prove2.me/theorems/85e07338-600a-420f-8666-218be3d44e4b
-- title:
--   Theorem 1: No low-energy trivial states
-- statement:
--   There is a deterministically explicit family of binary CSS check descriptions on $n$ qubits, and constants $\epsilon,c,a,b>0$, a locality bound $s$, and a threshold $n_0\ge1$, all independent of $n$. Explicit means that a deterministic polynomial-time function on unary $n$ outputs the actual row counts and both binary check matrices. For every $n\ge1$, both check matrices have row and column weights at most $s$, their total row count $m_n$ satisfies $an\le m_n\le bn$, and their associated projector terms $h_i=(I-X^{w_i})/2$ or $(I-Z^{w_i})/2$ act on at most $s$ qubits, commute, and annihilate a common unit vector. Let $H_n=\sum_i h_i$ be this unnormalized Hamiltonian. Every circuit $P$ of parallel one- and two-qubit unitaries on disjoint wires, starting from zero qubits and allowing arbitrary clean ancillas and discarded qubits, has an output density operator $\rho_P$ satisfying, for $n\ge n_0$,
--   $$
--   \operatorname{Tr}(H_n\rho_P)<\epsilon n
--   \quad\Longrightarrow\quad
--   \operatorname{depth}(P)\ge c\ln n.
--   $$
--
--   This is the existence of an NLTS Hamiltonian family. Quantifying over every preparation circuit gives the lower bound for mixed as well as pure low-energy states.
--
--   **Formalization Note** The deterministic interpretation of explicit and the CSS witness implementation are recorded for independent moderation; the theorem does not assume an NLTS guarantee on its family.
-- source:
--   NLTS Hamiltonians from good quantum codes, arXiv:2206.13228v4, Theorem 1: No low-energy trivial states, PDF p. 2. https://arxiv.org/abs/2206.13228v4 . PDF SHA-256: d7a1c5d8ee8ac147a6322005759342ac8154817d4e1534a9cc19b3da51b8875d.

import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model
set_option autoImplicit false

/-! Statements from Anshu--Breuckmann--Nirkhe, arXiv:2206.13228v4.
Theorem 5 and three construction-specific expansion claims are deferred in HARD.md.
All new definitions are specific to this paper. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P05

open PresentedCSS



























/-- Theorem 1, PDF p.2: explicit uniformly local commuting frustration-free Hamiltonians
with linearly many actual terms and logarithmic preparation depth below STRICT energy eps*n.
The generator convention is stated in nltsCheckEncoding and requires independent moderation. -/
theorem noLowEnergyTrivialStates :
    ∃ F : NLTSCheckFamily, ∃ generate : Complexity.Str → Complexity.Str,
      Complexity.PolyTimeComputable generate ∧
      (∀ n, generate (Complexity.unary n) = nltsCheckEncoding (F.checks n)) ∧
      ∃ eps c lower upper : ℝ, 0 < eps ∧ 0 < c ∧ 0 < lower ∧ 0 < upper ∧
      ∃ locality n0 : ℕ, 1 ≤ n0 ∧
      (∀ n ≥ 1, PresentedCSS.HasSparsity (F.checks n).HX locality ∧
        PresentedCSS.HasSparsity (F.checks n).HZ locality ∧
        lower*n ≤ (F.rowsX n+F.rowsZ n : ℕ) ∧ (F.rowsX n+F.rowsZ n : ℕ) ≤ upper*n ∧
        (∀ i, ActsOnAtMost locality (nltsTerms (F.checks n) i)) ∧
        (∀ i j, nltsTerms (F.checks n) i*nltsTerms (F.checks n) j =
          nltsTerms (F.checks n) j*nltsTerms (F.checks n) i) ∧
        ∃ psi : EuclideanSpace ℂ (Qubits n), IsState psi ∧
          ∀ i, act (nltsTerms (F.checks n) i) psi = 0) ∧
      ∀ n ≥ n0, ∀ P : NLTS.LayeredPreparationCircuit n,
        (NLTS.cssCheckHamiltonian (F.checks n)*NLTS.preparationOutputDensity P).trace.re < eps*n →
        c*Real.log n ≤ (NLTS.preparationDepth P : ℝ) := by sorry









end QAlgorithms.Papers.Independent.Independent1.P05
