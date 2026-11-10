-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_theorem_5_1
-- name    : RandomDimReduction.Channel.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:26:11.157809+00:00
-- url     : https://prove2.me/theorems/1382969d-1cf5-4d5e-a5c8-3bac987d723c
-- title:
--   Theorem 5.1 — efficient implementation of the Schur transform
-- statement:
--   There are global constants $c>0$ and $K\in\mathbb N$, a choice of labelled unitary Specht models, and a compatible family of exact Schur transforms $S_{d,n}$, all chosen before the error tolerance. For every positive $n,d$ and $0<\varepsilon<1$, there is a qubit circuit $C$ with
--   $$ |C|\le c(n+\log d+\log(1/\varepsilon)+2)^K,\qquad
--   \|\Phi_C\circ\mathrm{Enc}_{d,n}-\mathrm{Enc}^{\rm Schur}_{d,n}\circ\mathrm{Ad}_{S_{d,n}}\|_\diamond\le\varepsilon. $$
--   The basis encodings are fixed binary encodings and the norm is unhalved. This states full-unitary Schur implementation for arbitrary positive local dimension, rather than only a Schur measurement.
--
--   Differences from the source:
--   - reading: one Specht register is preserved between the d and k Schur transforms → one labelled unitary Specht model is shared across dimensions; reason: Algorithm 5.2 and Eq.(14) require compatible coordinates on this register
--   - encoding: direct sums over partitions whose height is at most the dimension → all partitions, with zero-dimensional absent Weyl factors; reason: empty factors contribute no coordinates or matrix entries
--   - encoding: poly(n, log d, log(1/ε)) elementary gates to ε accuracy → global c > 0 and natural K bound gates plus wires by c(n + log d + log(1/ε) + 2)^K, for 0 < ε < 1; reason: a single multivariate polynomial is bounded by this expression; logarithm bases only rescale constants, and idle ancillas can be omitted
--   - reading: elementary gates and diamond-norm implementation → unitary one- and two-qubit gates with zero ancillas and discarded outputs, in the unhalved diamond norm; reason: this fixes the elementary-gate convention and the stronger of the two diamond-distance normalizations
--   - encoding: operators on qudits or Schur registers implemented by a circuit → fixed binary encodings of basis indices, with a reference of the original input dimension; reason: basis isometries preserve the whole-map diamond comparison; the encodings are fixed before ε and dimension one uses zero qubits
--   - encoding: Schur transforms for positive n and d → a total natural-indexed family, with the implementation claim restricted to positive n and d; reason: degree zero has a one-dimensional trivial transform and positive degree at dimension zero has the empty transform; these extend the family without changing any source instance
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Theorem 5.1, p.15. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Circuits

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 5.1, p.15. The transforms and shared Specht models are chosen
before ε, with a fixed tuple encoding and global polynomial constants. -/
theorem theorem_5_1 :
    ∃ (c : ℝ) (K : ℕ), 0 < c ∧
      ∃ (κ : ∀ n, SpechtModel n) (S : ∀ n d, SchurTransform (κ n) d),
      ∀ n d : ℕ, 0 < n → 1 ≤ d → ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ C : Circuit (inputQubits n d) (schurQubits n d),
        (circuitSize C : ℝ) ≤ polyBound c K n d eps ∧
        diamond (fun X : Op (Word n d) =>
          circuitChannel C (encode n d X) - encodeSchur n d ((S n d).U * X * (S n d).Uᴴ)) ≤
            ENNReal.ofReal eps := by sorry

end RandomDimReduction.Channel
