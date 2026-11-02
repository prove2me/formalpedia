-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_simplexDistanceLimit
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.simplexDistanceLimit
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:47:38.672735+00:00
-- url     : https://prove2.me/theorems/3e50c150-d6c6-41d9-bbac-38c29e6bddef
-- title:
--   IV A: fixed-size simplex families approach the Chau threshold
-- statement:
--   Fix a number of codewords $m\ge2$. For every integer $j\ge0$, let $C_j$ be an actual equidistant code of $m$ distinct binary words of length $n_j\ge1$, without constant columns, and common distance $1\le d_j\le n_j$. Assume $d_j\to\infty$. Write $q_j$ for its symmetric-extendability threshold after Alice and Bob both filter on $C_j$, and $r_j$ for the repetition-code threshold at length $n_j$. Then
--
--   $$\lim_{j\to\infty}q_j=\frac{5-\sqrt5}{10},\qquad
--   \lim_{j\to\infty}(q_j-r_j)=0.$$
--
--   The family ranges only through feasible codes; existence at every distance and uniformity over unbounded code size are not claimed. Fixing $m$ follows the source's distance-limit reading, since the common factor depending on $n_j-d_j$ cancels when the Bell-diagonal operator is normalized.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 8, IV A: fixed-size simplex families approach the Chau threshold

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF p.8: fix m and range through actual feasible equidistant codes with d→infinity.
Neither existence at every distance nor uniform convergence in unbounded m is asserted. -/
theorem simplexDistanceLimit {m : ℕ} (hm : 2 ≤ m)
    (n d : ℕ → ℕ) (C : (j : ℕ) → Fin m → Qubits (n j))
    (hn : ∀ j, 1 ≤ n j) (hd0 : ∀ j, 1 ≤ d j) (hdn : ∀ j, d j ≤ n j)
    (hC : ∀ j, Function.Injective (C j)) (hd : ∀ j, Equidistant (C j) (d j))
    (hcols : ∀ j, NoConstantColumns (C j)) (hinfty : Filter.Tendsto d Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun j => bothThreshold (C j)) Filter.atTop (nhds chau) ∧
    Filter.Tendsto (fun j => bothThreshold (C j) - bobThreshold (repetition (Fin (n j))))
      Filter.atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
