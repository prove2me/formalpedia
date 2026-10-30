-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_quditStabilizerTesting
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.quditStabilizerTesting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:02:08.219254+00:00
-- url     : https://prove2.me/theorems/53171e66-9f20-44fa-930d-18f11553f785
-- title:
--   Qudit stabilizer testing
-- statement:
--   Let $d\geq2$ and $s\geq2$ with $\gcd(d,s)=1$. For any $n$, $\Pi_{s,\rm accept}=(I+V_s)/2$ is a valid effect on $2s$ copies. It accepts every pure stabilizer certainly. On any normalized pure state whose stabilizer fidelities are all at most $1-\varepsilon^2$, its acceptance probability obeys the following bound.
--
--   $$
--   p_{\rm accept}\leq1-C_{d,s}\varepsilon^2,\qquad C_{d,s}=\frac{1-(1-1/(4d^2))^{s-1}}2.
--   $$
--
--   This gives the source's qudit stabilizer testing in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 25, theorem-3.11

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.25, Theorem 3.11: composite d is allowed and all factors of C_{d,s} are retained. -/
theorem quditStabilizerTesting (d n s : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hs : 2 ≤ s) (hcop : Nat.Coprime d s) :
    QAlgorithms.IsEffect (quditTest d n s) ∧
    ∀ v : EuclideanSpace ℂ (ResidueRegister d n), ‖v‖ = 1 →
      (IsStabilizer v → QAlgorithms.effectProb (quditTest d n s)
        (tensorPower (2 * s) (QAlgorithms.pureDensity v)) = 1) ∧
      (∀ epsilon : ℝ, FarFromStabilizers v epsilon →
        QAlgorithms.effectProb (quditTest d n s) (tensorPower (2 * s) (QAlgorithms.pureDensity v)) ≤
          1 - soundnessConstant d s * epsilon ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
