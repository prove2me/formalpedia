-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_RTP_efficient
-- name    : RandomDimReduction.Channel.RTP_efficient
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-17T18:01:52.223736+00:00
-- url     : https://prove2.me/theorems/208fe0a0-8bc5-4972-9c75-400917ed4808
-- title:
--   Polynomial circuit implementation of the full reduction channel
-- statement:
--   There exist absolute constants $c>0$ and $K\in\mathbb N$, chosen independently of all dimensions and accuracy parameters, with the following property. For all positive $n,k,d$ with $k\le d$ and all $0<\varepsilon<1$, there is a qubit circuit $C$ such that
--   $$|C|\le c\big(n+\log d+\log(1/\varepsilon)+2\big)^K,$$
--   $$\|\Phi_C\circ\operatorname{Enc}_{d,n}-\operatorname{Enc}_{k,n}\circ R^{\mathrm{TP}}\|_\diamond\le\varepsilon.$$
--   Here $R^{\mathrm{TP}}$ is exactly Eq. (3), the encodings are the fixed binary basis encodings, and the diamond norm is unhalved. The circuit uses unitary one- and two-qubit gates, zero-initialized ancillas, and discarded non-output wires. Its size counts gates and qubit wires. The comparison holds on the entire operator space, with arbitrary entangled reference inputs and no support promise.
--
--   This is the operational conclusion of Theorem 1.1, established through the Schur implementation in Section 5.2. The circuit family is not required to be uniform.
-- source:
--   Angus Lowe and Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Theorem 1.1 p.2; Section 5.2 pp.15–19, Theorems 5.1 and 5.3 and Algorithm 5.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Moment
import Definitions.Def_RandomDimReduction_Channel_Circuits

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem RTP_efficient :
    ∃ (c : ℝ) (K : ℕ), 0 < c ∧
      ∀ n k d : ℕ, 0 < n → 1 ≤ k → k ≤ d →
      ∀ eps : ℝ, 0 < eps → eps < 1 →
        ∃ C : Circuit (inputQubits n d) (inputQubits n k),
          (circuitSize C : ℝ) ≤ polyBound c K n d eps ∧
          diamond (fun X : Op (Word n d) =>
            circuitChannel C (encode n d X) - encode n k (RTP n k d X)) ≤
              ENNReal.ofReal eps := by sorry

end RandomDimReduction.Channel
