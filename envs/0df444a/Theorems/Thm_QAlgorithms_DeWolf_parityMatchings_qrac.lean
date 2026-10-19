-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_parityMatchings_qrac
-- name    : QAlgorithms.DeWolf.parityMatchings_qrac
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-18T02:47:54.282057+00:00
-- url     : https://prove2.me/theorems/d56ac1c5-4538-459f-a8f2-1d12a1db2d84
-- title:
--   Disjoint parity matchings give a quantum random access code
-- statement:
--   Let $C:\{0,1\}^n\to\{0,1\}^N$, where $n,N\ge1$, and let $\eta,\kappa>0$. For each input coordinate $i$, suppose there is a family $M_i$ of pairwise disjoint subsets of the code coordinates, each of size at most two, together with bits $a_{i,t}$, satisfying
--
--   $$|M_i|\ge\eta N,$$
--
--   and, for every member $t$ of the family,
--
--   $$\Pr_{x\text{ uniform}}\!\left[x_i=a_{i,t}\oplus\bigoplus_{j\in t}C(x)_j\right]\ge\tfrac12+\kappa.$$
--
--   Then $\eta\kappa\le\tfrac12$, and there exist an integer $m$ and an encoding of the messages into $m$-qubit density matrices such that
--
--   $$m\le\log_2 N+2,$$
--
--   and every message bit can be recovered by a two-outcome measurement with average success probability at least
--
--   $$\tfrac12+\eta\kappa.$$
--
--   This is the quantum encoding step in the two-query locally decodable code lower bound. The additive two-qubit allowance includes constant reference coordinates for singleton predictors and padding to a power-of-two dimension. The hypotheses do not require that $C$ itself be an LDC. Empty predictor sets are permitted syntactically; positive correlation with an unbiased input bit rules them out.
--
--   **Formalization Note** Recovery uses the existing density-matrix and effect formulation `IsQRAC`; the average is uniform over all messages.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, arXiv:1907.09415v6, PDF pp. 142–143 (printed pp. 131–132), §15.3, Eq. (15.2) and quantum encoding proof preceding Theorem 5. Singleton and power-of-two padding made explicit. https://arxiv.org/pdf/1907.09415v6

import Definitions.Def_QAlgorithms_Defs_Information
set_option autoImplicit false

namespace QAlgorithms.DeWolf

/-- Disjoint one- and two-coordinate parity predictors yield a quantum random access code.
The extra constant coordinates allow singleton predictors, and zero padding allows arbitrary N. -/
theorem parityMatchings_qrac {n N : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N)
    (C : (Fin n → Bool) → (Fin N → Bool)) (η κ : ℝ)
    (hη : 0 < η) (hκ : 0 < κ)
    (hM : ∀ i : Fin n, ∃ M : Finset (Finset (Fin N)),
      (M : Set (Finset (Fin N))).PairwiseDisjoint id ∧
      (∀ t ∈ M, t.card ≤ 2) ∧ η * (N : ℝ) ≤ (M.card : ℝ) ∧
      ∃ a : Finset (Fin N) → Bool, ∀ t ∈ M,
        1 / 2 + κ ≤
          ((Finset.univ.filter fun x : Fin n → Bool =>
            x i = xor (a t) (decide (Odd (t.filter fun j => C x j = true).card))).card : ℝ) /
              (2 : ℝ) ^ n) :
    η * κ ≤ 1 / 2 ∧
      ∃ (m : ℕ) (ρ : (Fin n → Bool) → Matrix (Qubits m) (Qubits m) ℂ),
        (m : ℝ) ≤ Real.logb 2 (N : ℝ) + 2 ∧ IsQRAC ρ (1 / 2 + η * κ) := by sorry

end QAlgorithms.DeWolf
