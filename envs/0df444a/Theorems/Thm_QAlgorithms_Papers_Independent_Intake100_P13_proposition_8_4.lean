-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P13_proposition_8_4
-- name    : QAlgorithms.Papers.Independent.Intake100.P13.proposition_8_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:12:32.385631+00:00
-- url     : https://prove2.me/theorems/73d57eaf-6fe4-43c7-af03-f288527091ef
-- title:
--   Proposition 8.4
-- statement:
--   Let $A$ be a complex C*-algebra and $H$ any complex Hilbert space, including the zero space. Let $j_A:A\to M(A)$ be the canonical multiplier inclusion, and let $\rho:M(A)\to B(H)$ be a unital complex-linear star representation. The following conditions are equivalent:
--
--   1. Its restriction to $A$ is nondegenerate: if $\rho(j_A(a))v=0$ for every $a\in A$, then $v=0$.
--   2. There is a nondegenerate star representation $\pi:A\to B(H)$ for which $\rho$ is its canonical multiplier extension. Equivalently, $\rho\circ j_A=\pi$; nondegeneracy makes such a multiplier extension unique.
--   3. The map $\rho$ is continuous from the strict topology of $M(A)$ to the strong operator topology of $B(H)$, that is,
--   $$
--   \forall v\in H,\quad m\longmapsto\rho(m)v\text{ is strictly-to-norm continuous}.
--   $$
--   This characterizes multiplier representations arising from nondegenerate representations of $A$.
--
--   **Source correction.** The undefined $B$ in the printed third condition means $M(A)$. The unital representation convention is the one used in the proof, which uses $\rho(1)=\mathrm{Id}_H$.
-- source:
--   A complex semigroup approach to group algebras of infinite dimensional Lie groups, arXiv:0709.1062v1, PDF p. 38, Proposition 8.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P13

namespace QAlgorithms.Papers.Independent.Intake100.P13

open Set Filter Topology

noncomputable section

universe u v w

section Multipliers

variable (A : Type u) [NonUnitalCStarAlgebra A]

variable {A}

/-- Proposition 8.4, PDF pp. 38–39. SOURCE CORRECTIONS: B in clause
(3) means M(A); the representation of the unital algebra M(A) is unital,
as used by rho(1)=Id in the proof. Clause (2) is written as extension of
a nondegenerate pi; uniqueness of such an extension is Proposition 8.3's
Hilbert-space version, so this specifies the canonical extension.
All Hilbert spaces, including the zero space, are allowed. -/
theorem proposition_8_4
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (rho : DoubleCentralizer ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ((∀ v : H, (∀ a : A, rho (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A) a) v = 0) → v = 0) ↔
      (∃ pi : A →⋆ₙₐ[ℂ] (H →L[ℂ] H),
        (∀ v : H, (∀ a : A, pi a v = 0) → v = 0) ∧
        ∀ a : A, rho (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A) a) = pi a)) ∧
    ((∃ pi : A →⋆ₙₐ[ℂ] (H →L[ℂ] H),
        (∀ v : H, (∀ a : A, pi a v = 0) → v = 0) ∧
        ∀ a : A, rho (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := A) a) = pi a) ↔
      (∀ v : H, @Continuous (DoubleCentralizer ℂ A) H
        (strictTopology A) inferInstance (fun m => rho m v))) := by sorry

end Multipliers

end

end QAlgorithms.Papers.Independent.Intake100.P13
