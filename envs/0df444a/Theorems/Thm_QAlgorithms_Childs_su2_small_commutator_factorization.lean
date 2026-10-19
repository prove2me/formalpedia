-- Prove2me | Theorems.Thm_QAlgorithms_Childs_su2_small_commutator_factorization
-- name    : QAlgorithms.Childs.su2_small_commutator_factorization
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T19:58:56.480737+00:00
-- url     : https://prove2.me/theorems/b903afad-f07f-45f5-84db-164e8eaaf73e
-- title:
--   Small SU(2) elements admit balanced approximate commutator factorizations
-- statement:
--   For $r\ge0$, let $S_r=\{U\in SU(2):\|I-U\|\le r\}$, where the norm is the spectral norm, and write $[B,C]=BCB^{-1}C^{-1}$.
--
--   There exist constants $K>0$ and $\epsilon_0>0$ such that for every $0<\epsilon\le\epsilon_0$ and every $A\in S_{\epsilon^2}$, there are $B,C\in S_\epsilon$ with
--
--   $$\|A-[B,C]\|\le K\epsilon^3.$$
--
--   This is the geometric factorization step in the proof of Childs's commutator-net lemma, before replacing the factors by elements of an approximating net. The constants are uniform over $A$ and $\epsilon$.
-- source:
--   Andrew M. Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, §2.4, printed p. 9 (PDF page 17), proof of Lemma 2.3, construction of B and C immediately before equation (2.10), using facts (i), (iii), (iv). https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Circuit
set_option autoImplicit false

theorem QAlgorithms.Childs.su2_small_commutator_factorization :
    ∃ K : ℝ, 0 < K ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ A ∈ QAlgorithms.su2Ball (ε ^ 2),
        ∃ B ∈ QAlgorithms.su2Ball ε, ∃ C ∈ QAlgorithms.su2Ball ε,
          QAlgorithms.specNorm ((A : Matrix (Fin 2) (Fin 2) ℂ) -
            ((B * C * B⁻¹ * C⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
              Matrix (Fin 2) (Fin 2) ℂ)) ≤ K * ε ^ 3 := by sorry
