-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_cssComposition
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.cssComposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:16:30.136916+00:00
-- url     : https://prove2.me/theorems/694fd5f4-150c-4062-a1f7-6e7cea63b2b7
-- title:
--   CSS relation composition
-- statement:
--   Let $d$ be prime, $t\geq1$, and $N_1,N_2$ be defect subspaces. Construct $T=T_{N_1}\circ T_{N_2}$ by existential relational composition. Then $T\in\Sigma_{t,t}(d)$, its defects are $L=(N_1+N_2)\cap N_1^\perp$ and $M=(N_1+N_2)\cap N_2^\perp$, and its induced quotient map is $[y]\mapsto[x]$ whenever $x\in L^\perp$, $y\in M^\perp$, and $x-y\in N_1+N_2$. This is independent of the chosen representatives.
--
--   $$
--   R(T_{N_1})R(T_{N_2})=|N_1\cap N_2|^nR(T)=d^{n\dim(N_1\cap N_2)}R(T).
--   $$
--
--   This gives the source's css relation composition in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 40, lemma-4.25

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF pp.40--41, Lemma 4.25: computed CSS composition realizes precisely the data in (4.25). -/
theorem cssComposition (d t : ℕ) [NeZero d] [Fact (Nat.Prime d)] (ht : 1 ≤ t)
    (N M : Submodule (ZMod d) (ResidueRegister d t)) (hN : IsDefect N) (hM : IsDefect M) :
    let T := composeRelation (cssRelation N) (cssRelation M)
    IsStochasticLagrangian T ∧
    leftDefect T = (N ⊔ M) ⊓ perpendicular N ∧
    rightDefect T = (N ⊔ M) ⊓ perpendicular M ∧
    (∀ x y, (x, y) ∈ T ↔ x ∈ perpendicular (leftDefect T) ∧
      y ∈ perpendicular (rightDefect T) ∧ x - y ∈ N ⊔ M) ∧
    (∀ x y hx hy, x - y ∈ N ⊔ M →
      canonicalDefectMap T (defectClass (rightDefect T) y hy) = defectClass (leftDefect T) x hx) ∧
    (∀ n : ℕ, tensorRelation n (cssRelation N) * tensorRelation n (cssRelation M) =
      ((Nat.card ↥(N ⊓ M) : ℂ) ^ n) • tensorRelation n T ∧
      tensorRelation n (cssRelation N) * tensorRelation n (cssRelation M) =
        ((d : ℂ) ^ (n * Module.finrank (ZMod d) ↥(N ⊓ M))) • tensorRelation n T) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
