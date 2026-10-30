-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_qutritProductFiducials
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.qutritProductFiducials
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:24:46.368899+00:00
-- url     : https://prove2.me/theorems/0dc9ea9a-1867-49ca-bf7c-55180759d5e7
-- title:
--   Single product fiducials for qutrit third designs
-- statement:
--   In the stable range for prime $d$, the constructed Clifford moment expands in the independent class sums $R_i$. A normalized fiducial generates a projective $t$-design exactly when all coefficients except that of the permutation class vanish. In particular, for every $n\geq2$ there is a normalized single-qutrit vector $\psi$ for which $\psi^{\otimes n}$ generates a projective three-design. With $T$ the all-ones qutrit CSS relation, a normalized $\psi$ has this property exactly when the expectation below equals the indicated real root, which lies in $[1/3,3/5]$; $\psi$ may depend on $n$.
--
--   $$
--   \langle\psi^{\otimes3}|r(T)|\psi^{\otimes3}\rangle=\left(\frac3{3^n+2}\right)^{1/n}.
--   $$
--
--   This gives the source's single product fiducials for qutrit third designs in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 52, remark-6.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.52, Remark 6.4: criterion and existence of a single-qutrit product fiducial, depending on n. -/
theorem qutritProductFiducials (n : ℕ) (hn : 2 ≤ n) :
    Real.rpow (3 / ((3 : ℝ) ^ n + 2)) (1 / (n : ℝ)) ∈ Set.Icc (1 / 3) (3 / 5) ∧
    (∀ (d m t : ℕ) [NeZero d] [Fact (Nat.Prime d)], 1 ≤ t → t - 1 ≤ m →
      ∀ v : EuclideanSpace ℂ (ResidueRegister d m), ‖v‖ = 1 →
        cliffordMoment t v = ∑ F ∈ designClasses d t,
          (designCoefficients v F : ℂ) • designClassSum m F) ∧
    (∀ (d m t : ℕ) [NeZero d] [Fact (Nat.Prime d)], 1 ≤ t → t - 1 ≤ m →
      ∀ v : EuclideanSpace ℂ (ResidueRegister d m), ‖v‖ = 1 →
        (cliffordMoment t v = haarMoment d m t ↔ ∀ F ∈ designClasses d t,
          F ≠ designClassOf (graphRelation (1 : Matrix (Fin t) (Fin t) (ZMod d))) →
            designCoefficients v F = 0)) ∧
    (∀ v : EuclideanSpace ℂ (ResidueRegister 3 1), ‖v‖ = 1 →
      let psi : EuclideanSpace ℂ (ResidueRegister 3 n) := WithLp.toLp 2
        (fun x => ∏ j : Fin n, v (fun _ => x j))
      cliffordMoment 3 psi = haarMoment 3 n 3 ↔
        (inner ℂ (QAlgorithms.tensorPow 3 v)
          (QAlgorithms.act (tensorRelation 1 (cssRelation qutritDefect)) (QAlgorithms.tensorPow 3 v))).re =
            Real.rpow (3 / ((3 : ℝ) ^ n + 2)) (1 / (n : ℝ))) ∧
    (∃ v : EuclideanSpace ℂ (ResidueRegister 3 1), ‖v‖ = 1 ∧
      let psi : EuclideanSpace ℂ (ResidueRegister 3 n) := WithLp.toLp 2
        (fun x => ∏ j : Fin n, v (fun _ => x j))
      cliffordMoment 3 psi = haarMoment 3 n 3) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
