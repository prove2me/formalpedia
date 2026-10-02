-- Prove2me | Theorems.Thm_TeschlQM_Weyl_relativeBound_eq_zero
-- name    : TeschlQM.Weyl.relativeBound_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T23:41:25.994314+00:00
-- url     : https://prove2.me/theorems/ec4a7cf4-c20e-43d0-bff5-dd8dd57458d7
-- title:
--   Lemma 6.22 — a relatively compact operator has A-bound zero
-- statement:
--   Let $A$ be a self-adjoint operator in a complex Hilbert space $\mathfrak H$ and suppose $K$ is relatively compact with respect to $A$. Then the $A$-bound of $K$ is zero:
--   $$\inf\{ a \ge 0 \mid \exists b \ge 0\ \forall \psi \in \mathfrak D(A):\ \|K\psi\| \le a\|A\psi\| + b\|\psi\| \} = 0 .$$
--
--   Relatively compact perturbations are therefore infinitesimally small, and the Kato–Rellich theorem applies to them with any bound.
--
--   **Formalization Note.** The $A$-bound is valued in $[0,\infty]$ and equals $\infty$ when $K$ is not $A$ bounded, so the conclusion includes that $K$ is $A$ bounded. Relative compactness is (5.12): $K R_A(z)$ is compact for one $z \in \rho(A)$, with $\mathfrak D(A) \subseteq \mathfrak D(K)$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 148, Lemma 6.22

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_IsRelativelyCompact
import Definitions.Def_TeschlQM_Shared_relativeBound

namespace TeschlQM.Weyl

/-- Teschl, Lemma 6.22, p. 148. Let `A` be self-adjoint and suppose `K` is relatively compact with
respect to `A`. Then the `A`-bound of `K` is zero. (The `A`-bound is valued in `[0, ∞]` and is `∞`
for an operator that is not `A` bounded, so the conclusion includes that `K` is `A` bounded.) -/
theorem relativeBound_eq_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A K : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hK : TeschlQM.Shared.IsRelativelyCompact K A) :
    TeschlQM.Shared.relativeBound A K = 0 := by sorry

end TeschlQM.Weyl
