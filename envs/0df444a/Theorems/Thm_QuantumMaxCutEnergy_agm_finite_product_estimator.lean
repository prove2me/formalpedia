-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm_finite_product_estimator
-- name    : QuantumMaxCutEnergy.agm_finite_product_estimator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T14:26:09.425897+00:00
-- url     : https://prove2.me/theorems/10f7d9da-e70e-4056-907a-258e269d3dbb
-- title:
--   Finite-bit product-estimation subroutine with explicit approximation slack
-- statement:
--   There exists one uniform randomized classical polynomial-time algorithm P returning a nonnegative rational number. On every graph G with nonnegative rational edge weights, every prescribed fair-bit outcome is at most OPT(G), and the finite uniform expected output is at least 0.953(OPT(G)+W(G))/3. Arbitrary weight bit lengths, zero-weight graphs and the empty graph are included. The factor 0.953 reserves explicit slack below the literature product-approximation guarantee. A proof must provide the finite-bit SDP algorithm, rounding, precision bounds, failure handling and the mathematical comparison with the QMC optimum.
-- source:
--   Anshu, Gosset and Morenz, TQC2020, Theorem1 p7:4 and Eqs18–19 pp7:8–7:9, used in proof of Theorem3. https://doi.org/10.4230/LIPIcs.TQC.2020.7 . The fixed factor 0.953 below 0.956 supplies room for finite-precision computation and amplification; those implementation steps remain part of this open theorem.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators

theorem QuantumMaxCutEnergy.agm_finite_product_estimator :
    ∃ P : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime P ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (∀ r : Fin (QuantumMaxCutEnergy.randomBits P G) → Bool,
          (P.run G (List.ofFn r) : ℝ) ≤ QuantumMaxCutEnergy.optimum G) ∧
        (0.953 : ℝ) * (QuantumMaxCutEnergy.optimum G + (∑ e, (G.weights e : ℝ))) / 3 ≤
          (∑ r : Fin (QuantumMaxCutEnergy.randomBits P G) → Bool,
            (P.run G (List.ofFn r) : ℝ)) /
            (Fintype.card (Fin (QuantumMaxCutEnergy.randomBits P G) → Bool) : ℝ) := by sorry
