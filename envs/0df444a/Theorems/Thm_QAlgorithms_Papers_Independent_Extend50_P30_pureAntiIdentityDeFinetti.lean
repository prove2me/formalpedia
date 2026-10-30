-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_pureAntiIdentityDeFinetti
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.pureAntiIdentityDeFinetti
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:27:06.810929+00:00
-- url     : https://prove2.me/theorems/18ab1d8e-39d8-45ce-b66f-cc97c68c6321
-- title:
--   Pure-state anti-identity stabilizer de Finetti theorem
-- statement:
--   Let $t\geq6$, and let $\Psi$ be a normalized symmetric state on $t$ blocks of $n$ qubits. Suppose the anti-identity fixes it on some explicitly embedded set of six distinct blocks. Let $s<t$ be divisible by six, with $s=0$ allowed. A distribution on pure stabilizer states approximates the first $s$ blocks with the following error.
--
--   $$
--   \frac12\left\|\Psi_{1\ldots s}-\sum_Sp(S)S^{\otimes s}\right\|_1\leq6\sqrt{2^{n+1}}\sqrt{s/t}.
--   $$
--
--   This gives the source's pure-state anti-identity stabilizer de finetti theorem in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 55, theorem-7.3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF pp.55--56, Theorem 7.3: t need not be divisible by six, but s is; the six-block embedding exists. -/
theorem pureAntiIdentityDeFinetti (n t s : ℕ) (ht : 6 ≤ t) (hs : s < t) (hdiv : 6 ∣ s)
    (v : EuclideanSpace ℂ (QuditCopies 2 n t)) (hv : ‖v‖ = 1) (hsym : IsPermutationSymmetric v)
    (hinv : ∃ e : Fin 6 ↪ Fin t, QAlgorithms.act (embeddedAntiIdentity e) v = v) :
    ∃ p : QuditOperator 2 n → ℝ, IsDistributionOn (stabilizers 2 n) p ∧
      QAlgorithms.traceNorm (copyPrefixReduction s (Nat.le_of_lt hs) (QAlgorithms.pureDensity v) -
        stabilizerMixture s (stabilizers 2 n) p) / 2 ≤
          6 * Real.sqrt ((2 : ℝ) ^ (n + 1)) * Real.sqrt ((s : ℝ) / t) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
