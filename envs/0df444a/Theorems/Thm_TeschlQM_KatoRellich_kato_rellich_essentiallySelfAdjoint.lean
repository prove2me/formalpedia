-- Prove2me | Theorems.Thm_TeschlQM_KatoRellich_kato_rellich_essentiallySelfAdjoint
-- name    : TeschlQM.KatoRellich.kato_rellich_essentiallySelfAdjoint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T22:34:05.779562+00:00
-- url     : https://prove2.me/theorems/907e97e9-0c66-4078-abd9-dd9f877b4664
-- title:
--   Theorem 6.4 — Kato–Rellich (essentially self-adjoint case)
-- statement:
--   Let $A$ be an essentially self-adjoint operator and $B$ a symmetric operator in a complex Hilbert space $\mathfrak{H}$, and suppose the $A$-bound of $B$ is less than one. Then $A + B$, with domain $\mathfrak{D}(A + B) = \mathfrak{D}(A)$, is essentially self-adjoint, and
--   $$\mathfrak{D}(\overline{A}) \subseteq \mathfrak{D}(\overline{B}), \qquad \overline{A + B} = \overline{A} + \overline{B}.$$
--   If moreover $A$ is bounded from below by $\gamma$, and $a \in [0,1)$, $b \ge 0$ are constants for which (6.1) holds, then $A + B$ is bounded from below by $\gamma - \max(a|\gamma| + b, b/(1 - a))$.
--
--   This is the form of the theorem used when $A$ is known only on a core, e.g. $-\Delta$ on smooth compactly supported functions.
--
--   **Formalization Note.** Closures are Mathlib's `LinearPMap.closure`. The lower bound corrects the book's printed $b/(a-1)$ to $b/(1-a)$; see the goal theorem `kato_rellich` for the counterexample.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 135, Theorem 6.4, Eq. (6.3)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Shared_IsEssentiallySelfAdjoint
import Definitions.Def_TeschlQM_KatoRellich_IsRelativelyBounded
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy

namespace TeschlQM.KatoRellich

open scoped ENNReal

/-- Teschl, Theorem 6.4 (Kato–Rellich), p. 135, essentially self-adjoint case. If `A` is essentially
self-adjoint and `B` is symmetric with `A`-bound less than one, then `A + B` with
`𝔇(A + B) = 𝔇(A)` is essentially self-adjoint, `𝔇(Ā) ⊆ 𝔇(B̄)` and `\overline{A + B} = Ā + B̄`.
If moreover `A ≥ γ` and (6.1) holds with constants `a < 1`, `b`, then
`A + B ≥ γ - max(a|γ| + b, b/(1 - a))` (the book's `b/(a - 1)` corrected, as in `kato_rellich`). -/
theorem kato_rellich_essentiallySelfAdjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsEssentiallySelfAdjoint A) (hB : TeschlQM.Shared.IsSymmetric B)
    (hbound : relativeBound A B < 1) :
    (A + B).domain = A.domain ∧ TeschlQM.Shared.IsEssentiallySelfAdjoint (A + B) ∧
      A.closure.domain ≤ B.closure.domain ∧ (A + B).closure = A.closure + B.closure ∧
      ∀ γ a b : ℝ, a < 1 → IsRelativelyBoundedWith A B a b → TeschlQM.Shared.IsBoundedBelowBy A γ →
        TeschlQM.Shared.IsBoundedBelowBy (A + B) (γ - max (a * |γ| + b) (b / (1 - a))) := by sorry

end TeschlQM.KatoRellich
