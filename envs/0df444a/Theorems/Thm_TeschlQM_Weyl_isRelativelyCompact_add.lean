-- Prove2me | Theorems.Thm_TeschlQM_Weyl_isRelativelyCompact_add
-- name    : TeschlQM.Weyl.isRelativelyCompact_add
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T23:49:25.430048+00:00
-- url     : https://prove2.me/theorems/b4ff9722-9c90-4aa6-afd0-ae730544a1a1
-- title:
--   Lemma 6.23 — relative compactness passes from A to A + B when B has A-bound < 1
-- statement:
--   Let $A$ be a self-adjoint operator in a complex Hilbert space $\mathfrak H$ and $B$ a symmetric operator whose $A$-bound is less than one. If $K$ is relatively compact with respect to $A$, then it is also relatively compact with respect to $A + B$, the operator $\psi \mapsto A\psi + B\psi$ on $\mathfrak D(A)$:
--   $$K R_A(z) \in \mathfrak C(\mathfrak H) \text{ for one } z \in \rho(A) \ \Longrightarrow\ K R_{A+B}(z') \in \mathfrak C(\mathfrak H) \text{ for one } z' \in \rho(A+B).$$
--
--   By the Kato–Rellich theorem $A + B$ is self-adjoint, so this lets one add relatively compact perturbations on top of relatively bounded ones.
--
--   **Formalization Note.** $A + B$ is Mathlib's sum of partial linear maps, with domain $\mathfrak D(A) \cap \mathfrak D(B)$, which equals $\mathfrak D(A)$ because the $A$-bound of $B$ is finite. The $A$-bound is valued in $[0,\infty]$, so "less than one" also asserts that $B$ is $A$ bounded.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 148, Lemma 6.23

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_IsRelativelyCompact
import Definitions.Def_TeschlQM_Shared_relativeBound
import Definitions.Def_TeschlQM_Shared_IsSymmetric

namespace TeschlQM.Weyl

/-- Teschl, Lemma 6.23, p. 148. Suppose `A` is self-adjoint and `B` is symmetric with `A`-bound less
than one. If `K` is relatively compact with respect to `A`, then it is also relatively compact with
respect to `A + B` (Mathlib's sum of partial maps, with domain `𝔇(A) ∩ 𝔇(B) = 𝔇(A)`). -/
theorem isRelativelyCompact_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B K : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : TeschlQM.Shared.IsSymmetric B)
    (hbound : TeschlQM.Shared.relativeBound A B < 1) (hK : TeschlQM.Shared.IsRelativelyCompact K A) :
    TeschlQM.Shared.IsRelativelyCompact K (A + B) := by sorry

end TeschlQM.Weyl
