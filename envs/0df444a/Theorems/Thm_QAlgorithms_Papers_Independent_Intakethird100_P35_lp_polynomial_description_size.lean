-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P35_lp_polynomial_description_size
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P35.lp_polynomial_description_size
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:21:22.265586+00:00
-- url     : https://prove2.me/theorems/8bf2015e-9567-470b-8544-4f073f6471a0
-- title:
--   Unnumbered main claim: polynomial LP description size
-- statement:
--   Consider the four optimized flow programs (12), (19), (21), and (37) on a finite network with $n$ vertices, $e$ undirected edges, $d$ directed channel labels, $r\ge1$ terminal pairs, and a terminal group $S$ with $|S|\ge2$. Each directed label is mapped to its underlying undirected edge; its supplied finite nonnegative channel coefficient is multiplied by its frequency. The explicit coefficient arrays include both orientations, flow nonnegativity and conservation, frequency normalization and bounds, shared or independent edge budgets as appropriate, and the slack constraints for worst-case and connectivity objectives. Write $D_j$ for the number of real scalar entries in the dense constraint matrix, right-hand side, and objective of program $j$. There is an absolute positive integer $C$ such that, uniformly over all these data,
--
--   $$D_j\le C\,(n+e+d+r+|S|+1)^8,\qquad j\in\{12,19,21,37\}.$$
--
--   Thus their combinatorial descriptions have polynomial size. The deliberately loose polynomial bound concerns scalar-entry counts; exact solution time or bit complexity for arbitrary real coefficients is not asserted. Redundant zero endpoint-conservation rows and one fixed-zero unused slack in the single/total encodings preserve the feasible flows and objective.
-- source:
--   Linear programs for entanglement and key distribution in the quantum internet, arXiv:1809.03120v3, PDF p. 2, Unnumbered main claim: polynomial LP description size

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P35

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P35

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2,16: the four actual LP coefficient arrays have polynomial size.
The universal constant precedes all network data. The generous degree-eight
bound avoids endorsing p.16's inconsistent exact slack counts. This is solely
the combinatorial description-size claim; no arbitrary-real polynomial-time
solver claim or operational-capacity claim is included. -/
theorem lp_polynomial_description_size :
    ∃ Csize : ℕ, 0 < Csize ∧
    ∀ (n e d r : ℕ) (G : EdgeGraph n (Fin e)) (hSimple : IsSimple G)
      (a b : Fin n) (hab : a ≠ b) (hr : 0 < r)
      (s t : Fin r → Fin n) (hst : ∀ i, s i ≠ t i)
      (S : Finset (Fin n)) (hS : 2 ≤ S.card)
      (edgeOf : Fin d → Fin e) (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j),
      let bound := Csize * (n + e + d + r + S.card + 1) ^ 8
      descriptionSize (optimizedLP G (fun _ : Fin 1 => a)
        (fun _ : Fin 1 => b) edgeOf c false false) ≤ bound ∧
      descriptionSize (optimizedLP G s t edgeOf c false false) ≤ bound ∧
      descriptionSize (optimizedLP G s t edgeOf c false true) ≤ bound ∧
      descriptionSize (optimizedLP G (fun p : TerminalPair S => p.val.1)
        (fun p : TerminalPair S => p.val.2) edgeOf c true true) ≤ bound := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P35

end
