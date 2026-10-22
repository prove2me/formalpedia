-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P01_weakSchur_measurement_polylog_dimension
-- name    : QAlgorithms.Papers.Independent.Gap20.P01.weakSchur_measurement_polylog_dimension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:13:32.498202+00:00
-- url     : https://prove2.me/theorems/7d896cb7-63ab-4bad-825e-53449fd480a1
-- title:
--   Weak Schur measurement has polynomial dependence on log d
-- statement:
--   Let $n,d\ge1$ be integers and let $|\psi\rangle$ be a unit vector in $(\mathbb C^d)^{\otimes n}$ with its computational basis. For every partition $\lambda$ of $n$ into at most $d$ parts, let $\Pi_\lambda$ be the full isotypic projector for the tensor-factor permutation action. The ideal finite-group Fourier measurement for $G=S_n$ and $R=P$ has
--
--   $$
--   \Pr[\lambda]=\|\Pi_\lambda\psi\|_2^2.
--   $$
--
--   This is the same label distribution as full Schur analysis followed by measuring only $\lambda$. In addition, there are absolute constants $C>0$ and an integer $k\ge0$ such that, for every $n,d\ge1$ and $0<\epsilon<1$, one circuit on $m$ qubits, using arbitrary unitary one-qubit gates and CNOT, satisfies
--
--   $$
--    m,\;\mathrm{size}(\mathcal C)\ \le\ C\bigl(n+\log d+\log(1/\epsilon)+1\bigr)^k
--   $$
--
--   and, simultaneously for every normalized input, its measured output law $p_{\mathcal C,\psi}$ satisfies
--
--   $$
--   \sum_{\lambda}\left|p_{\mathcal C,\psi}(\lambda)-\|\Pi_\lambda\psi\|_2^2\right|+p_{\mathcal C,\psi}(\mathrm{invalid})\le\epsilon.
--   $$
--
--   The physical word is encoded as its base-$d$ integer in the last $n\lceil\log_2 d\rceil$ input wires, with other input wires zero. The output shape occupies the leading $n\lceil\log_2(n+1)\rceil$ bits; its row lengths are digits in base $n+1$. Invalid padded codes are explicitly counted. This states an efficient measurement of Schur subspaces; it makes no claim about approximating the full coherent Schur output or retaining the physical state inside each subspace.
-- source:
--   Efficient Quantum Circuits for Schur and Clebsch-Gordan Transforms, arXiv:quant-ph/0407082v4, PDF p. 4, Schur specialization after Eq.(11); abstract PDF p.1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P01

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Gap20.P01

open QAlgorithms.Papers.Independent.Support21.P09 (Rep UnitaryRep elementaryGates)

variable {G L I : Type} [Group G] [Fintype G] [Fintype L]
  [Fintype I]

/-- PDF pp.1,3--4: weak Schur measurement, distinct from the full coherent
Schur transform. The ideal Fourier circuit's lambda marginal is precisely
the full isotypic-projector probability. It has standard elementary-circuit
approximations polynomial in n, log d and log(1/epsilon), uniformly over
normalized inputs. The error is the l1 distance of outcome laws, including
invalid padded codes; this implies total-variation error at most epsilon/2.
The circuit and absolute polynomial constants precede every input state.
No approximation of the full Schur output vector or within-irrep state
preservation is claimed. -/
theorem weakSchur_measurement_polylog_dimension :
    (∀ (n d : ℕ), 0 < n → 0 < d →
      ∀ psi : EuclideanSpace ℂ (Fin n → Fin d), IsState psi →
      ∀ lambda : QAlgorithms.Schur.Partition d n,
        (∑ a : Fin (Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda)),
          ∑ b : Fin (Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda)),
          ∑ x : Fin n → Fin d, Complex.normSq (idealSchurAmplitude psi lambda a b x)) =
        ‖act (QAlgorithms.Schur.isotypicProjector lambda) psi‖ ^ 2) ∧
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (n d : ℕ), 0 < n → 0 < d →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      ∃ (m : ℕ) (circuit : Circuit
          {g : Gate | g ∈ elementaryGates ∧ (g.arity = 1 ∨ g = Gate.ofMatrix2 cnot)} m),
        n * Nat.clog 2 d ≤ m ∧ shapeWidth n ≤ m ∧
        (m : ℝ) ≤ C * ((n : ℝ) + Real.log d + Real.log (1 / epsilon) + 1) ^ k ∧
        (circuit.size : ℝ) ≤
          C * ((n : ℝ) + Real.log d + Real.log (1 / epsilon) + 1) ^ k ∧
        ∀ psi : EuclideanSpace ℂ (Fin n → Fin d), IsState psi →
          (∑ lambda : QAlgorithms.Schur.Partition d n,
            |probEvent (act circuit.unitary (encodedPhysical m psi)) (reportsShape m lambda) -
              ‖act (QAlgorithms.Schur.isotypicProjector lambda) psi‖ ^ 2|) +
            probEvent (act circuit.unitary (encodedPhysical m psi)) (invalidShape (d := d) (n := n) m)
            ≤ epsilon := by sorry

end QAlgorithms.Papers.Independent.Gap20.P01

end
