-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_repeatedQuditTesting
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.repeatedQuditTesting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:03:02.839658+00:00
-- url     : https://prove2.me/theorems/a1c2ad27-079c-4ab9-a9e0-4e2e27c52ba3
-- title:
--   Repeated qudit test and local implementation
-- statement:
--   Fix $d\geq2$ and $s\geq2$ coprime to $d$. There is $C>0$, depending only on these fixed parameters, such that for every $n$ and $\varepsilon>0$, a test using $k=2sr$ copies accepts every stabilizer certainly and rejects every normalized state with stabilizer fidelity at most $1-\varepsilon^2$ with probability at least $2/3$. The effect is the tensor product of $r$ copies of $\Pi_{s,\rm accept}$. Moreover $V_s$ is a product of $n$ embedded copies of a fixed $2s$-qudit unitary; its controlled version is therefore a circuit of $n$ fixed-size controlled blocks.
--
--   $$
--   k\leq\frac{C}{C_{d,s}\varepsilon^2},\qquad p_{\rm reject}\geq\frac23.
--   $$
--
--   This gives the source's repeated qudit test and local implementation in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 26, corollary-3.13

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.26, Corollary 3.13: constants may depend on fixed d,s, never on n,epsilon,psi.
The displayed local-unitary factorization supplies the efficient implementation at fixed d,s. -/
theorem repeatedQuditTesting (d s : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hs : 2 ≤ s) (hcop : Nat.Coprime d s) :
    (quditInvolution d 1 s ∈ Matrix.unitaryGroup (QuditCopies d 1 (2 * s)) ℂ) ∧
    (∀ n : ℕ, quditInvolution d n s =
      (List.ofFn (fun j : Fin n => embeddedLocal j (quditInvolution d 1 s))).prod) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ r : ℕ, ∃ A : CopyTest d n,
        A.copies = 2 * s * r ∧ HEq A.accept (repeatEffect r (quditTest d n s)) ∧
        (A.copies : ℝ) ≤ C / (soundnessConstant d s * epsilon ^ 2) ∧
        ∀ v : EuclideanSpace ℂ (ResidueRegister d n), ‖v‖ = 1 →
          (IsStabilizer v → A.prob v = 1) ∧
          (FarFromStabilizers v epsilon → A.prob v ≤ 1 / 3) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
