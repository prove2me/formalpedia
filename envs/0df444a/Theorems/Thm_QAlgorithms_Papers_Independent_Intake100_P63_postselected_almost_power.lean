-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_postselected_almost_power
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.postselected_almost_power
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:21:09.171279+00:00
-- url     : https://prove2.me/theorems/c50cf449-c0cc-4c89-b11d-3de2d40584d2
-- title:
--   Lemma III.5: post-selected exponential almost-power approximation
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space, $n\ge1$, and let $\theta\in H$ and $\Psi_n\in H^{\otimes n}$ be unit vectors, with $\Psi_n$ permutation symmetric. Assume $c=|\langle\Psi_n\mid\theta^{\otimes n}\rangle|>0$. A normalized almost-power vector along a unit vector $\theta$ on $N$ sites is a unit vector in the symmetric subspace intersected with the complex span of tensors having at least $N-r$ factors equal to $\theta$; the remaining at most $r$ factors may have an arbitrary joint vector. For each $0\le m\le n$ there is a unit vector $\Psi_{n,m}$ on $n-m$ sites such that
--   $$
--   |\Psi_{n,m}\rangle\langle\Psi_{n,m}|\le c^{-2}\operatorname{Tr}_{1,\ldots,m}|\Psi_n\rangle\langle\Psi_n|.
--   $$
--   For every $0\le r\le n-m$, the same vector admits a normalized almost-power approximation $\Psi_{n,m,r}$ along $\theta$ with
--   $$
--   \big\||\Psi_{n,m}\rangle\langle\Psi_{n,m}|-|\Psi_{n,m,r}\rangle\langle\Psi_{n,m,r}|\big\|_1
--   \le2\sqrt2\,c^{-1}\exp\!\left(-\frac{mr}{2n}\right).
--   $$
--
--   The exponential is natural. Positive overlap is the domain needed for the printed inverse powers and normalized postselection; zero overlap is undefined in the source.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 13, Lemma III.5: post-selected exponential almost-power approximation

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

/-- PDF pp.13--14 Lemma III.5 Eqs.(68),(69). SOURCE DOMAIN CORRECTION:
positive overlap and n>0 are the domains of the printed inverse powers and
exponent. At zero overlap the source's normalized postselection is undefined. -/
theorem postselected_almost_power {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (n : ℕ) (hn : 0 < n) (theta : Vec I) (htheta : IsState theta)
    (psi : Vec (Copies I n)) (hpsi : IsState psi) (hsym : CopySymmetric psi)
    (hoverlap : 0 < ‖inner ℂ psi (tensorPow n theta)‖)
    (m : ℕ) (hm : m ≤ n) :
    ∃ post : Vec (Copies I (n - m)), IsState post ∧
      ((((‖inner ℂ psi (tensorPow n theta)‖ ^ 2)⁻¹ : ℝ) : ℂ) •
        discardPrefix m hm (pureDensity psi) - pureDensity post).PosSemidef ∧
      ∀ r, r ≤ n - m → ∃ approx : Vec (Copies I (n - m)),
        AlmostPower theta (n - m) r approx ∧
        traceNorm (pureDensity post - pureDensity approx) ≤
          2 * Real.sqrt 2 * ‖inner ℂ psi (tensorPow n theta)‖⁻¹ *
            Real.exp (-((m : ℝ) * r) / (2 * n)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
