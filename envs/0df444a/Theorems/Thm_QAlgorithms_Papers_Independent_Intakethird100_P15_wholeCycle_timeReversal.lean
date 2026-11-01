-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P15_wholeCycle_timeReversal
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P15.wholeCycle_timeReversal
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:03:55.456959+00:00
-- url     : https://prove2.me/theorems/735b65ac-053f-4090-bacb-18fcd3737b3c
-- title:
--   Whole-cycle quantum time reversal
-- statement:
--   Let $\mathcal H$ be a nonzero complex Hilbert space with a nonempty finite or countable complete orthonormal basis real in a fixed conjugation. The self-adjoint Hamiltonian $H(t)$ is real in that conjugation, periodic with period $t_0>0$, and satisfies $H(-t)=H(t)$. Start at this symmetry origin and observe an integer number of full cycles. Let $U$ be the well-defined unitary strong limit of the chronological infinitesimal slice products, with each slice equal to $\exp(+i\tau H/\hbar)$ and $\hbar>0$.
--
--   For every finite slicing at the symmetry origin, and for its unitary strong limit, the adjoint equals entrywise conjugation in the fixed real basis:
--   $$U^\dagger=\overline U.$$
--   Explicitly, $\langle i|U^\dagger|j\rangle=\overline{\langle i|U|j\rangle}$ for all basis labels $i,j$; equivalently $U_{ij}=U_{ji}$. The same coefficient identity holds for each finite chronological slice product.
--
--   This is the reversal identity underlying the fluctuation relations, derived from the real Hamiltonians and palindromic slicing.
-- source:
--   A Quantum Fluctuation Theorem, arXiv:cond-mat/0007360v2, PDF p. 2, Whole-cycle time reversal, (3)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P15

namespace QAlgorithms.Papers.Independent.Intakethird100.P15

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P37 (transition)

open QAlgorithms.Papers.Independent.Support21.P03 (reflectedLaw)

open QAlgorithms.Papers.Independent.Next46.P01 (extendedExpectation)

open scoped ENNReal Topology

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {ι : Type v} {Ω : Type w} [MeasurableSpace Ω]

/-- Kurchan, PDF p.2, (3). Finite slice products and their well-defined unitary
strong limit have adjoint equal to entrywise conjugation in the fixed real basis.
The inverse of a unitary is its adjoint; scalar `star` is complex conjugation.
This derives reversal rather than including reversal in `CyclicDrive`. -/
theorem wholeCycle_timeReversal [Countable ι] [Nonempty ι]
    (b : HilbertBasis ι ℂ E) (d : CyclicDrive (Ω := Ω) b) :
    (∀ n i j,
      inner ℂ (b i) ((chronologicalEvolution (List.ofFn (d.slices n))).symm (b j)) =
        star (inner ℂ (b i) (chronologicalEvolution (List.ofFn (d.slices n)) (b j)))) ∧
    (∀ i j, inner ℂ (b i) (d.evolution.symm (b j)) =
      star (inner ℂ (b i) (d.evolution (b j)))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P15
