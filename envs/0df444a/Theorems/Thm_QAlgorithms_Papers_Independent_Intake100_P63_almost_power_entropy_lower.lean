-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_almost_power_entropy_lower
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.almost_power_entropy_lower
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:22:30.913785+00:00
-- url     : https://prove2.me/theorems/34acb1e3-88f3-4019-9f5b-1d6889c67be0
-- title:
--   Lemma III.7: relative-entropy lower bound on almost-power reductions
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space and let $\rho\in\mathcal D(H)$ be a normalized density operator. For each positive integer $n$, let $M_n\subseteq\mathcal D(H^{\otimes n})$ be closed and convex. Assume that one fixed full-rank state $\sigma$ has $\sigma^{\otimes n}\in M_n$ for every positive $n$, that every single-copy partial trace preserves the family, that tensor products map $M_n\times M_m$ into $M_{n+m}$, and that conjugation by every copy permutation preserves $M_n$. Define $E_{M_n}(\xi)=\inf_{\omega\in M_n}D_2(\xi\Vert\omega)$, using base-two relative entropy with value $+\infty$ on failed support inclusion, and define $E_M^\infty(\rho)=\inf_{n\ge1}E_{M_n}(\rho^{\otimes n})/n$.
--
--   Let $\theta\in H\otimes H_E$ be a unit purification of $\rho$, with $H_E$ a copy of $H$ and $\lambda_{\max}(\rho)<1$. Let $m(n),r(n)$ be nonnegative integer sequences with $m(n)+r(n)\le n$ for positive $n$, and $m(n)/n,r(n)/n\to0$. A normalized almost-power vector along a unit vector $\theta$ on $N$ sites is a unit vector in the symmetric subspace intersected with the complex span of tensors having at least $N-r$ factors equal to $\theta$; the remaining at most $r$ factors may have an arbitrary joint vector. For every sequence of normalized almost-power vectors $\Psi_n$ along $\theta$ on $n-m(n)$ sites with at most $r(n)$ defects,
--   $$
--   E_M^\infty(\rho)\le\liminf_{n\to\infty}\frac1n E_{M_{n-m(n)}}\!\left(\operatorname{Tr}_{E^{\otimes(n-m(n))}}|\Psi_n\rangle\langle\Psi_n|\right).
--   $$
--
--   The denominator remains n. The lower bound is a conclusion about arbitrary almost-power sequences.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 18, Lemma III.7: relative-entropy lower bound on almost-power reductions

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.18 Lemma III.7 Eq.(102): arbitrary normalized almost-power sequences,
with denominator n, not n-m. The environmental space is a copy of H. -/
theorem almost_power_entropy_lower {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (M : (n : ℕ) → Set (Mat (Copies I n))) (hM : stateSetAxioms M)
    (theta : Vec (I × I)) (htheta : IsState theta) (hmixed : MixedMarginal theta)
    (m r : ℕ → ℕ) (hm : Sublinear m) (hr : Sublinear r)
    (psi : (n : ℕ) → Vec (Copies (I × I) (n - m n)))
    (hpsi : ∀ n, 0 < n → AlmostPower theta (n - m n) (r n) (psi n))
    (hrange : ∀ n, 0 < n → m n + r n ≤ n) :
    regularizedSetEntropy M (traceRight (pureDensity theta)) ≤
      liminf (fun n => setEntropy (M (n - m n))
        (discardEnvironment (pureDensity (psi n))) / (n : ℝ≥0∞)) atTop := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
