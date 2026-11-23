-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_algorithm52_efficient_of_schur
-- name    : RandomDimReduction.Channel.algorithm52_efficient_of_schur
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:35:13.53681+00:00
-- url     : https://prove2.me/theorems/8dfadca7-7b20-43e9-a56c-cffc886a8210
-- title:
--   Algorithm 5.2 is efficient given efficient Schur transforms
-- statement:
--   Fix a compatible family of Schur transforms and suppose that each transform $S_{n,d}$ has a circuit approximation with the whole-channel diamond-norm guarantee and polynomial size bound of Theorem 5.1. Then there are constants $c>0$ and $K\in\mathbb N$, depending only on the constants in that supplied Schur bound, such that for every $n,k,d$ with $0<n$, $1\le k\le d$, and every $0<\varepsilon<1$, Algorithm 5.2 has a circuit $C$ satisfying
--   $$
--   |C|\le c\bigl(n+\log d+\log(1/\varepsilon)+2\bigr)^K,
--   $$
--   and
--   $$
--   \bigl\|\Phi_C\circ\operatorname{Enc}_{d,n}-\operatorname{Enc}_{k,n}\circ\operatorname{Alg}_{5.2}(S_{n,d},S_{n,k})\bigr\|_\diamond\le\varepsilon.
--   $$
--   This is the circuit-combination step for Algorithm 5.2: apply the Schur transform, measure the partition label, output the maximally mixed state on high labels, otherwise preserve the Specht register and replace the Weyl register by a maximally mixed one, and apply the inverse Schur transform. No support promise is imposed, and the approximation concerns the entire channel. The supplied forward Schur circuits also suffice for the inverse step by reversing the gate list and adjoining every gate.
--
--   **Formalization Note.** Circuits use arbitrary unitary one- and two-qubit gates, zero-initialized ancillas and discarded wires; size counts both wires and gates. The encodings and the unhalved diamond norm are those fixed in `RandomDimReduction_Channel_Circuits` and `RandomDimReduction_Channel_Diamond`.
-- source:
--   Angus Lowe and Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Algorithm 5.2 p.16 and the efficient-implementation deduction from Theorem 5.1 on pp.15–16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Moment
import Definitions.Def_RandomDimReduction_Channel_Circuits
import Definitions.Def_RandomDimReduction_Channel_Algorithm

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Algorithm 5.2, p.16: an efficient implementation of the two Schur
transforms yields an efficient implementation of the whole four-step
algorithm. The circuit comparison is on the whole channel, in diamond norm. -/
theorem algorithm52_efficient_of_schur
    (c₀ : ℝ) (K₀ : ℕ) (hc₀ : 0 < c₀)
    (κ : ∀ n, SpechtModel n) (S : ∀ n d, SchurTransform (κ n) d)
    (hS : ∀ n d : ℕ, 0 < n → 1 ≤ d → ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ C : Circuit (inputQubits n d) (schurQubits n d),
        (circuitSize C : ℝ) ≤ polyBound c₀ K₀ n d eps ∧
        diamond (fun X : Op (Word n d) =>
          circuitChannel C (encode n d X) - encodeSchur n d ((S n d).U * X * (S n d).Uᴴ)) ≤
            ENNReal.ofReal eps) :
    ∃ (c : ℝ) (K : ℕ), 0 < c ∧
      ∀ n k d : ℕ, 0 < n → 1 ≤ k → k ≤ d →
      ∀ eps : ℝ, 0 < eps → eps < 1 →
        ∃ C : Circuit (inputQubits n d) (inputQubits n k),
          (circuitSize C : ℝ) ≤ polyBound c K n d eps ∧
          diamond (fun X : Op (Word n d) =>
            circuitChannel C (encode n d X) -
              encode n k (algorithm52 (S n d) (S n k) X)) ≤
                ENNReal.ofReal eps := by sorry
