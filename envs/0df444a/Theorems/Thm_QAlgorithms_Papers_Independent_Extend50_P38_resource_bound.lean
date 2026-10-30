-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P38_resource_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P38.resource_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:55:10.170972+00:00
-- url     : https://prove2.me/theorems/f048f660-86e4-4087-857a-42fc4d3061a2
-- title:
--   Resource-independent fidelity bound and small-port attainment
-- statement:
--   Let $d,N\geq1$. Every normalized pure resource on $2N$ qudits and every $N$-outcome Alice POVM, followed by Bob's uncorrected port retention, obey
--
--   $$F\leq\frac{N}{d^2},\qquad f\leq\frac{d+N}{d(d+1)}.$$
--
--   Here $F$ is entanglement fidelity and $f$ is Haar-average pure-input fidelity. If $f>2/(d+1)$, then $N>d$. When $N\leq d$, there exist orthogonal computational output states $|e_i\rangle$ and a POVM for which the separable pure resource $|0\rangle_A^{\otimes N}\otimes\bigotimes_i|e_i\rangle_{B_i}$ attains equality in both bounds. This distinguishes the universal upper bound from the small-$N$ regime in which it is sharp.
-- source:
--   Asymptotic teleportation scheme as a universal programmable quantum processor, arXiv:0807.4568v2, PDF p. 4, Unnumbered upper bound and separable construction

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P38

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions; neither is re-declared in this module.

open QAlgorithms.Papers.Independent.Frontier18.P14 (singlet)

open QAlgorithms.Papers.Independent.Renew46.P01 (SpinPath)

/-- PDF p.4: resource-independent bound, its separable attainment for N≤d, and
the necessary N>d condition to beat the classical average-fidelity benchmark. -/
theorem resource_bound (d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    (∀ O : Matrix (Ports d N) (Ports d N) ℂ, ValidResource O →
      ∀ M : Fin N → Matrix (AC d N) (AC d N) ℂ, IsPOVM M →
        QuditFidelity.entanglementFidelity d hd (teleport O M) ≤ (N : ℝ) / (d : ℝ) ^ 2 ∧
        QuditFidelity.averageFidelity d hd (teleport O M) ≤
          ((d : ℝ) + (N : ℝ)) / ((d : ℝ) * ((d : ℝ) + 1)) ∧
        (2 / ((d : ℝ) + 1) < QuditFidelity.averageFidelity d hd (teleport O M) → d < N)) ∧
    (N ≤ d → ∃ e : Fin N ↪ Fin d,
      ValidResource (separableOperator hd e) ∧
      ∃ M : Fin N → Matrix (AC d N) (AC d N) ℂ, IsPOVM M ∧
        QuditFidelity.entanglementFidelity d hd (teleport (separableOperator hd e) M) =
          (N : ℝ) / (d : ℝ) ^ 2 ∧
        QuditFidelity.averageFidelity d hd (teleport (separableOperator hd e) M) =
          ((d : ℝ) + (N : ℝ)) / ((d : ℝ) * ((d : ℝ) + 1))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P38

end
