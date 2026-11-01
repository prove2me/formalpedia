-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P84_nonprojectiveMeasurementExample
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P84.nonprojectiveMeasurementExample
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:06:49.636315+00:00
-- url     : https://prove2.me/theorems/28a2e962-4e0d-4c50-afe1-89cc2a30d0d5
-- title:
--   Example 1: nonprojective measurements can preserve relative entropy
-- statement:
--   Fix real numbers $0<\mu<1/2$ and $0<x<1$. On $\mathbb C^3$ set $D_1=\operatorname{diag}(1-2\mu,\mu,\mu)$, $D_2=I/3$, and
--
--   $$
--   E_1=\operatorname{diag}(1,0,0),\qquad
--   E_2=\begin{pmatrix}0&0&0\0&x&z\0&\bar z&1-x\end{pmatrix},\qquad
--   E_3=\begin{pmatrix}0&0&0\0&1-x&-z\0&-\bar z&x\end{pmatrix}.
--   $$
--
--   There exists $r>0$ such that for every complex $z$ with $|z|<r$, these effects are positive semidefinite and sum to $I$. Writing $\mu_i(j)=\operatorname{Tr}(D_iE_j)$ for the corresponding three-outcome probability laws, one has
--
--   $$
--   S(\mu_1,\mu_2)=S(D_1,D_2).
--   $$
--
--   Here $S$ denotes classical or quantum relative entropy with natural logarithms, as appropriate. This explicit family demonstrates that an entropy-preserving measurement need not be projective.
--
--   **Formalization Note** The probability laws are represented by their computed diagonal density matrices. The radius is existential and is quantified before $z$, matching the source's phrase “small enough.”
-- source:
--   Monotonicity of quantum relative entropy revisited, arXiv:quant-ph/0209053v1, PDF p. 7, Example 1: nonprojective measurements can preserve relative entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P84

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions, inspected at their recorded source locations.

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower marginalAB)

/-- Petz, arXiv:quant-ph/0209053v1, PDF p.7, Example 1.
The positive radius formalizes exactly the source's "modulus small enough";
it is chosen before z and no unprinted sharp boundary is imposed. -/
theorem nonprojectiveMeasurementExample (mu x : ℝ)
    (hmu0 : 0 < mu) (hmu1 : mu < 1 / 2) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      IsPOVM (exampleEffects x z) ∧
      qRelEntropy
        (measurementDensity (exampleEffects x z) (petzExampleDensity mu))
        (measurementDensity (exampleEffects x z) exampleReference) =
      qRelEntropy (petzExampleDensity mu) exampleReference := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P84

end
