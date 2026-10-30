-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_defectIsomorphismExtension
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.defectIsomorphismExtension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:12:36.564284+00:00
-- url     : https://prove2.me/theorems/fd7f7e00-2145-4cbf-b429-fcafb62623d7
-- title:
--   Extending a defect isomorphism
-- statement:
--   For prime $d$ and $t\geq1$, let $N,M$ be defect subspaces and $J:N^\perp/N\to M^\perp/M$ an invertible linear map preserving the quadratic form and the all-ones class. A stochastic isometry extends its action on every quotient representative.
--
--   $$
--   \exists O\in O_t(d):\quad ON=M,\qquad[Ox]=J[x]\quad(x\in N^\perp).
--   $$
--
--   This gives the source's extending a defect isomorphism in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 38, lemma-4.20

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.38, Lemma 4.20: every quotient representative is included in the induced-map equation. -/
theorem defectIsomorphismExtension (d t : ℕ) [NeZero d] [Fact (Nat.Prime d)] (ht : 1 ≤ t)
    (N M : Submodule (ZMod d) (ResidueRegister d t)) (hN : IsDefect N) (hM : IsDefect M)
    (J : DefectIsomorphism N M) :
    ∃ O : StochasticOrthogonal d t,
      (fun x => O.val.mulVec x) '' (N : Set _) = (M : Set _) ∧
      ∀ x (hx : x ∈ perpendicular N), ∃ hy : O.val.mulVec x ∈ perpendicular M,
        J.linearEquiv (defectClass N x hx) = defectClass M (O.val.mulVec x) hy := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
