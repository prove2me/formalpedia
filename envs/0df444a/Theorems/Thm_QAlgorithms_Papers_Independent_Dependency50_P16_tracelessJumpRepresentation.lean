-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_tracelessJumpRepresentation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.tracelessJumpRepresentation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:49:56.109552+00:00
-- url     : https://prove2.me/theorems/da0a0cd8-e26c-42f3-9624-1c8f027e6f26
-- title:
--   Unnumbered traceless jump representation
-- statement:
--   Every general CP-generator representation on $M_n(\mathbb C)$, $n\ge2$, admits a traceless-jump representation of the same generator:
--
--   $$\exists K',W_1,\ldots,W_r:\quad G_{K',W}=G_{K,V},\qquad\operatorname{tr}(W_k)=0\quad\text{for every }k.$$
--
--   The compensation of $K$ is retained through equality of actual generators. The scalar-shift construction keeps the finite number of jumps; no trace-preservation condition is imposed.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 31, Unnumbered traceless jump representation

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.31, Unnumbered traceless jump representation. This uses only scalar-shift freedom, not the false unrestricted coisometry transformation. r=0 is allowed. -/
theorem tracelessJumpRepresentation {n r : ℕ} (hn : 2 ≤ n) (K : Mat n) (V : Fin r → Mat n) :
    ∃ (Knew : Mat n) (W : Fin r → Mat n),
      cpGenerator Knew W = cpGenerator K V ∧ ∀ k, (W k).trace = 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
