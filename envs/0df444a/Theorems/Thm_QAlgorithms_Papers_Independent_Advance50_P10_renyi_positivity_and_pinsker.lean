-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_renyi_positivity_and_pinsker
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.renyi_positivity_and_pinsker
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:33:48.153931+00:00
-- url     : https://prove2.me/theorems/de6f7736-cb8d-4ace-a777-c4c306464ee8
-- title:
--   Proposition II.3: positivity, equality cases, and Pinsker
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $A,B\ge0$ with $\operatorname{Tr}A\le1$ and $\operatorname{Tr}B\le1$. For $0<\alpha<1$,
--
--   $$S_\alpha(A\|B)\ge0,\qquad S_\alpha(A\|B)=0\iff A=B\text{ and }\operatorname{Tr}A=1.$$
--
--   If $\operatorname{Tr}A=1$, then for every finite $\alpha\ge1$ the divergence is nonnegative and is zero exactly when $A=B$. If also $\operatorname{Tr}B=1$, then
--
--   $$S_\alpha(A\|B)\ge\tfrac12\|A-B\|_1^2\qquad(\alpha\ge1).$$
--
--   Here $\|\cdot\|_1$ is the unhalved trace norm. These clauses preserve the different normalization domains of positivity and Pinsker’s inequality.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 4, Proposition II.3: positivity, equality cases, and Pinsker

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P10

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Advance50.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Dependency50.P18 (logBits)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Bridge50.P45 (tensorEntries lifted comparison)

-- Density subtypes below reuse the frozen PSD/trace-one predicate directly.

-- The source uses Borel laws, with the weak topology on probability measures.

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityBorelSpace

/-- Proposition II.3, PDF p.4: positivity, exact equality cases, and the printed
one-half Pinsker constant, with the three different normalization domains. -/
theorem renyi_positivity_and_pinsker {I : Type} [Fintype I] [DecidableEq I]
    (A B : Operator I) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrA : A.trace.re ≤ 1) (htrB : B.trace.re ≤ 1) :
    (∀ a : ℝ, 0 < a → a < 1 → 0 ≤ petzRelativeBits a A B ∧
      (petzRelativeBits a A B = 0 ↔ A = B ∧ A.trace.re = 1)) ∧
    (A.trace.re = 1 → ∀ a : ℝ, 1 ≤ a → 0 ≤ petzRelativeBits a A B ∧
      (petzRelativeBits a A B = 0 ↔ A = B)) ∧
    (A.trace.re = 1 → B.trace.re = 1 → ∀ a : ℝ, 1 ≤ a →
      ((1 / 2 * traceNorm (A - B) ^ 2 : ℝ) : EReal) ≤ petzRelativeBits a A B) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
