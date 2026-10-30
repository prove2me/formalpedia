-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_mixedAntiIdentityDeFinetti
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.mixedAntiIdentityDeFinetti
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:29:44.099746+00:00
-- url     : https://prove2.me/theorems/c262f7fd-fa7f-4870-827d-97550c3deffb
-- title:
--   Mixed-state anti-identity stabilizer de Finetti theorem
-- statement:
--   Let $\rho$ be a positive semidefinite trace-one state on $t\geq6$ blocks of $n$ qubits. Suppose it commutes with all block permutations and with the anti-identity on one embedded set of six distinct blocks. For $s<t$ divisible by six, including zero, there exists a probability distribution on maximally mixed stabilizer code states satisfying the following bound.
--
--   $$
--   \frac12\left\|\rho_{1\ldots s}-\sum_\sigma p(\sigma)\sigma^{\otimes s}\right\|_1\leq6\sqrt2\,2^n\sqrt{s/t}.
--   $$
--
--   This gives the source's mixed-state anti-identity stabilizer de finetti theorem in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 58, theorem-7.7

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.58, Theorem 7.7: all permutations, one six-block anti-identity, and the printed 2^n factor. -/
theorem mixedAntiIdentityDeFinetti (n t s : ℕ) (ht : 6 ≤ t) (hs : s < t) (hdiv : 6 ∣ s)
    (rho : Matrix (QuditCopies 2 n t) (QuditCopies 2 n t) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsym : ∀ p : Equiv.Perm (Fin t),
      rho * permutationOperator 2 n t p = permutationOperator 2 n t p * rho)
    (hinv : ∃ e : Fin 6 ↪ Fin t, rho * embeddedAntiIdentity e = embeddedAntiIdentity e * rho) :
    ∃ p : QuditOperator 2 n → ℝ, IsDistributionOn (mixedStabilizers 2 n) p ∧
      QAlgorithms.traceNorm (copyPrefixReduction s (Nat.le_of_lt hs) rho -
        stabilizerMixture s (mixedStabilizers 2 n) p) / 2 ≤
          6 * Real.sqrt 2 * (2 : ℝ) ^ n * Real.sqrt ((s : ℝ) / t) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
