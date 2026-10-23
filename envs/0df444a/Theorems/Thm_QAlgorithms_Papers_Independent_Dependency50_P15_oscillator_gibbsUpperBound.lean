-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P15_oscillator_gibbsUpperBound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P15.oscillator_gibbsUpperBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:28:10.198157+00:00
-- url     : https://prove2.me/theorems/7c199100-54b7-4219-82cf-00f06beb0109
-- title:
--   Eq. (19), entropy inequality: explicit multimode Gibbs entropy upper bound
-- statement:
--   Fix an integer $\ell\ge1$ and positive mode energies $a_i=\hbar\omega_i>0$. On the full Fock space $\ell^2(\mathbb N^\ell)$ let $H$ be the number Hamiltonian with eigenvalue $\sum_{i=1}^{\ell}a_i n_i$ on occupation $n$, so its vacuum has energy zero. For every finite budget $E\ge0$, the Gibbs state constructed from this full spectrum satisfies
--
--   $$S(\gamma_H(E))\le\ell\log_2 e+\sum_{i=1}^{\ell}\log_2\!\left(1+\frac{E}{\ell a_i}\right).$$
--
--   Here $e$ is the base of the natural logarithm and entropy is in bits. This useful entropy upper bound is the final inequality in Eq.(19); the separate optimizing equality on that line is deferred because it is false for unequal frequencies.
-- source:
--   Tight uniform continuity bounds for quantum entropies: conditional entropy, relative entropy distance and energy constraints, arXiv:1507.07775v6, PDF p. 10, Eq. (19), entropy inequality: explicit multimode Gibbs entropy upper bound

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P15

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P15

open QAlgorithms.Papers.Independent.Information100.P08 (bellVector)

/-- Eq.(19), PDF p.10, entropy upper inequality ONLY. The false equal-allocation
maximizing equality is separately deferred, with its explicit counterexample in HARD.md.
The spectrum includes every Fock occupation and arbitrary positive mode frequencies. -/
theorem oscillator_gibbsUpperBound (ell : ℕ) (hell : 1 ≤ ell)
    (a : Fin ell → ℝ) (ha : ∀ i, 0 < a i) (E : ℝ) (hE : 0 ≤ E) :
    gibbsEntropy (oscillatorEnergy a) E ≤
      (ell : ℝ) * Real.logb 2 (Real.exp 1) +
        ∑ i, Real.logb 2 (1 + E / ((ell : ℝ) * a i)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P15

end
