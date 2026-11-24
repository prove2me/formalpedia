-- Prove2me | Theorems.Thm_ValiantBorder_boundedDegreeCircuitProgram
-- name    : ValiantBorder.boundedDegreeCircuitProgram
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:03:51.130404+00:00
-- url     : https://prove2.me/theorems/2ad99ecb-1c09-4292-91c8-12d481057719
-- title:
--   A weighted program for the low-degree part of a circuit
-- statement:
--   For the input lengths and circuit sizes in the contracting-field argument, a bounded arithmetic circuit can be compiled into a weighted binary-tree program that evaluates the indicated sum of homogeneous components on encoded words. The bounds control running time, the program description, and the height and size of its table of named constants.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/LowDeg.lean#L42).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/LowDeg.lean#L42.

import Definitions.Def_ValiantBorder_programWord
import Definitions.Def_VP_VNP_all_fields

open NS1 MvPolynomial

theorem ValiantBorder.boundedDegreeCircuitProgram (H : ℕ) (hH : 32 ≤ H) : ∃ c : ℕ, ∀ v a, 100 ≤ v → c * (a + H + 2) * lg v ≤ v →
    ∀ (A : Type) [CommRing A] (R : Type) [CommRing R] [Algebra A R] (θ : List Bool → A) (s : ℕ)
      (p : MvPolynomial (Fin (v ^ (H - 32) + 1) × Option Bool) R), s ≤ v ^ a → Statement.Computes p s →
    ∃ (K : KT R) (D : Tree), (∀ z : Tree, z.size ≤ v ^ (H - 32) → Hl θ (Fm.ofTree D) z ∧
        (∀ r ∈ evl θ (Fm.ofTree D) z, r.cost ≤ v ^ (H - 16) ∧ ∀ q ∈ r.bill, K.InB 1 q) ∧
        val K.lk (evl θ (Fm.ofTree D) z) = ∑ i ∈ Finset.range (v ^ (H - 32) + 1 + 1),
          MvPolynomial.eval (codeB R (v ^ (H - 32) + 1) (tbits z)) (MvPolynomial.homogeneousComponent i p)) ∧
      K.nds ≤ v ^ (3 * a + H + 20) ∧ D.size ≤ v ^ (3 * a + H + 20) ∧ K.ht ≤ (3 * a + H + 20) * lg v := by sorry
