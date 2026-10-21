-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P45_general_coefficient_maximum
-- name    : QAlgorithms.Papers.Independent.Renew46.P45.general_coefficient_maximum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:46:46.25199+00:00
-- url     : https://prove2.me/theorems/9d010dd5-c4e2-499c-b49c-b4e3dae626b4
-- title:
--   General-dimensional coefficient maximum and unique maximizing irreducible labels
-- statement:
--   Let $d\ge2$, $N\ge1$ and $M>N$. For a CP unital complex-linear cloning map $T:B((\mathbb C^d)^{\otimes M})\to B(\operatorname{Sym}^N\mathbb C^d)$ that is covariant under the actual $U(d)$ tensor representations and invariant under output permutations, let $\omega(T)$ be the real generator coefficient normalized by $T(\sum_{k=1}^M a_{(k)})=\omega(T)\partial\pi_N^+(a)$ for traceless $a$. Let $P_r$ be the actual Bose projector and $D_r=\binom{d+r-1}{r}$. The explicit map with dual
--   $$
--   \widehat T_*(\rho)=\frac{D_N}{D_M}P_M(\rho\otimes I_{M-N})P_M
--   $$
--   is a covariant permutation-invariant cloning map, and
--   $$
--   \omega(T)\le\omega(\widehat T)=\frac{M+d}{N+d}.
--   $$
--   This gives the attained maximum on the stated covariant domain. It does not assert uniqueness over unsymmetrized devices; a maximizing auxiliary $U(d)$ weight, when used, is dual rather than an unqualified positive symmetric-power label.
--
--   On the actual admissible irreducible blocks of Proposition 5, the same bound holds for the Casimir coefficient $\omega_N(m,n)$. An admissible block attains it, and
--   $$
--   \omega_N(m,n)=\frac{M+d}{N+d}\quad\Longleftrightarrow\quad m=(M,0,\ldots,0),\quad n=(0,\ldots,0,N-M).
--   $$
--   Admissibility includes an actual isometric inclusion of the first carrier into $H^{\otimes M}$ and an actual isometric intertwiner from $\operatorname{Sym}^N H$ into the product of the two irreducible carriers. The weights are their dominant integral highest weights for the actual complexified differentials. The negative last entry $N-M$ is integral subtraction. This equality case characterizes irreducible labels, without asserting uniqueness of arbitrary cloning devices.
-- source:
--   Optimal Cloning of Pure States, Judging Single Clones, arXiv:quant-ph/9807010v1, PDF p. 10, §III E, conclusion

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P45.unitaryMeasurable

/-- PDF pp.8–10, III E and Lemma 6: general-d coefficient maximum attained by
Eq.(3), over covariant permutation-invariant cloners, with the unique maximizing
actual irreducible labels. The auxiliary highest weight is dual,
(0,...,0,N-M), as fixed by p.9. No unrestricted device uniqueness is asserted. -/
theorem general_coefficient_maximum (d N M : ℕ) (hd : 2 ≤ d)
    (hN : 1 ≤ N) (hNM : N < M) :
    IsCloning (optimalCloner (d := d) (Nat.le_of_lt hNM)) ∧
    IsCloningCovariant (optimalCloner (d := d) (Nat.le_of_lt hNM)) ∧
    IsPermutationInvariant (optimalCloner (d := d) (Nat.le_of_lt hNM)) ∧
    cloneCoefficient (d := d) (by omega) (optimalCloner (d := d) (Nat.le_of_lt hNM)) =
      ((M : ℝ) + d) / ((N : ℝ) + d) ∧
    (∀ T : CloneFunction d N M, IsCloning T → IsCloningCovariant T → IsPermutationInvariant T →
      cloneCoefficient (d := d) (by omega) T ≤ ((M : ℝ) + d) / ((N : ℝ) + d)) ∧
    (∃ B : CloningBlock d N M, ∃ m n : Fin d → ℤ,
      HasHighestWeight B.pa m ∧ HasHighestWeight B.pb n ∧
      weightCoefficient N m n = ((M : ℝ) + d) / ((N : ℝ) + d)) ∧
    ∀ B : CloningBlock d N M, ∀ m n : Fin d → ℤ,
      HasHighestWeight B.pa m → HasHighestWeight B.pb n →
      weightCoefficient N m n ≤ ((M : ℝ) + d) / ((N : ℝ) + d) ∧
      (weightCoefficient N m n = ((M : ℝ) + d) / ((N : ℝ) + d) ↔
        m = symmetricWeight d M ∧
        n = (fun j : Fin d => if j.val + 1 = d then (N : ℤ) - M else 0)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P45

end
