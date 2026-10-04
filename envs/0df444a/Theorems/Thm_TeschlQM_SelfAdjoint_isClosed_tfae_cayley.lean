-- Prove2me | Theorems.Thm_TeschlQM_SelfAdjoint_isClosed_tfae_cayley
-- name    : TeschlQM.SelfAdjoint.isClosed_tfae_cayley
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:23:18.128524+00:00
-- url     : https://prove2.me/theorems/69a965ed-793d-4731-90b8-d5892b7ee338
-- title:
--   Lemma 2.27 — A closed iff 𝔇(V), Ran(V) or V closed
-- statement:
--   Let $A$ be a symmetric operator on a complex Hilbert space and $V$ its Cayley transform. The following are equivalent:
--   - $A$ is closed;
--   - $\mathfrak{D}(V) = \operatorname{Ran}(A + \mathrm{i})$ is closed;
--   - $\operatorname{Ran}(V) = \operatorname{Ran}(A - \mathrm{i})$ is closed;
--   - $V$ is closed.
--
--   **Formalization Note.** Closedness of an operator is Mathlib's `LinearPMap.IsClosed` (closed graph); closedness of a subspace is `IsClosed` of the underlying set. $\operatorname{Ran}(V)$ is `Set.range V`. The equivalence is `List.TFAE`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 83, Lemma 2.27

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_IsCayleyTransform

namespace TeschlQM.SelfAdjoint

/-- Teschl, Lemma 2.27 (p. 83): for a symmetric `A` with Cayley transform `V`, the following are
equivalent: `A` is closed; `𝔇(V) = Ran(A + i)` is closed; `Ran(V) = Ran(A - i)` is closed;
`V` is closed. -/
theorem isClosed_tfae_cayley {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A V : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (hV : IsCayleyTransform A V) :
    List.TFAE [A.IsClosed, IsClosed (V.domain : Set H), IsClosed (Set.range V), V.IsClosed] := by sorry

end TeschlQM.SelfAdjoint
