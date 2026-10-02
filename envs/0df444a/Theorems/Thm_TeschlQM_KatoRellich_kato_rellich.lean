-- Prove2me | Theorems.Thm_TeschlQM_KatoRellich_kato_rellich
-- name    : TeschlQM.KatoRellich.kato_rellich
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T22:28:46.354986+00:00
-- url     : https://prove2.me/theorems/5b1db298-0240-4422-954a-5217bff8ea8f
-- title:
--   Theorem 6.4 — Kato–Rellich (self-adjoint case, with the lower bound (6.3))
-- statement:
--   Let $A$ be a self-adjoint operator and $B$ a symmetric operator in a complex Hilbert space $\mathfrak{H}$, and suppose the $A$-bound of $B$ is less than one. Then $A + B$, with domain $\mathfrak{D}(A + B) = \mathfrak{D}(A)$, is self-adjoint.
--
--   If moreover $A$ is bounded from below by $\gamma$, and $a \in [0,1)$, $b \ge 0$ are constants for which (6.1) holds, then $A + B$ is bounded from below by
--   $$\gamma - \max\Big(a|\gamma| + b,\; \frac{b}{1 - a}\Big).$$
--
--   This is the basic perturbation theorem for self-adjoint operators: it gives self-adjointness of Schrödinger operators $-\Delta + V$ for potentials that are small relative to the kinetic energy.
--
--   **Formalization Note.** The book prints the lower bound (6.3) as $\gamma - \max(a|\gamma| + b, b/(a-1))$. Because $b/(a-1) \le 0$, that expression equals $\gamma - a|\gamma| - b$, and this is false: in $\mathbb{C}^2$ with $A = \operatorname{diag}(0, 6.57)$ ($\gamma = 0$), $B$ the real symmetric matrix with entries $-4.00, 3.32; 3.32, -9.10$, and $a = 0.931$, the best $b$ is $\approx 5.97$ while the lowest eigenvalue of $A + B$ is $\approx -6.66 < -b$. The statement uses $b/(1 - a)$, which is Kato's constant (*Perturbation Theory for Linear Operators*, Thm V.4.11). "$A$-bound less than one" is `relativeBound A B < 1` in $[0,\infty]$, which includes relative boundedness. The sum $A + B$ is Mathlib's sum of `LinearPMap`s, defined on $\mathfrak{D}(A) \cap \mathfrak{D}(B)$; the first conjunct asserts that this is $\mathfrak{D}(A)$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 135, Theorem 6.4, Eq. (6.3)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_KatoRellich_IsRelativelyBounded
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy

namespace TeschlQM.KatoRellich

open scoped ENNReal

/-- Teschl, Theorem 6.4 (Kato–Rellich), p. 135, self-adjoint case with the lower bound (6.3).
If `A` is self-adjoint and `B` is symmetric with `A`-bound less than one, then `A + B` with
`𝔇(A + B) = 𝔇(A)` is self-adjoint. If moreover `A ≥ γ` and (6.1) holds with constants `a < 1`, `b`,
then `A + B ≥ γ - max(a|γ| + b, b/(1 - a))`. The book prints `b/(a - 1)`, which is false
(see the moderation notes); `b/(1 - a)` is the corrected constant (Kato, Thm V.4.11). -/
theorem kato_rellich {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : TeschlQM.Shared.IsSymmetric B)
    (hbound : relativeBound A B < 1) :
    (A + B).domain = A.domain ∧ IsSelfAdjoint (A + B) ∧
      ∀ γ a b : ℝ, a < 1 → IsRelativelyBoundedWith A B a b → TeschlQM.Shared.IsBoundedBelowBy A γ →
        TeschlQM.Shared.IsBoundedBelowBy (A + B) (γ - max (a * |γ| + b) (b / (1 - a))) := by sorry

end TeschlQM.KatoRellich
