-- Prove2me | Theorems.Thm_PertComp_lemma_2_7
-- name    : PertComp.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:28.492047+00:00
-- url     : https://prove2.me/theorems/dd12e02b-cab7-4761-83ff-d260696f5780
-- title:
--   Lemma 2.7: $(\partial f)\,\Box\,(\partial g)=\partial(f\,\Box\,g)$
-- statement:
--   Let $X$ be a reflexive real Banach space, let $f,g\in\Gamma_0(X)$, and suppose that $0\in\operatorname{sri}(\operatorname{dom} f^*-\operatorname{dom} g^*)$ (a condition in $X^*$). Then
--   $$(\partial f)\,\Box\,(\partial g)=\partial(f\,\Box\,g),$$
--   where the left-hand side is the parallel sum (2.3) of the subdifferentials and the right-hand side is the subdifferential of the infimal convolution (2.9).
--
--   Differences from the source:
--   - encoding: functions with values in ]−∞, +∞] or [−∞, +∞] → EReal-valued functions; a function of Γ₀ never takes ⊥; reason: Lean convention; same instances
--   - encoding: reflexive real Banach space → NormedSpace ℝ with [CompleteSpace] and IsReflexive (the canonical map into the bidual is onto); reason: Mathlib has no reflexivity class; same spaces
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Lemma 2.7, p.7

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Conj
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_PertComp_IsReflexive
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PertComp_sri
import Definitions.Def_PertComp_infConv
import Definitions.Def_PertComp_parSum

namespace PertComp

open Pointwise

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Lemma 2.7**, p.7: let `X` be a reflexive real
Banach space, `f, g ∈ Γ₀(X)`, and suppose `0 ∈ sri (dom f* − dom g*)`. Then
`(∂f) □ (∂g) = ∂(f □ g)`.

**Formalization Note.** `□` on the left is the parallel sum (2.3) (`parSum`), on the right the
infimal convolution (2.9) (`infConv`); the identity is between set-valued maps `X → 2^{X*}`. The
qualification condition lives in `X*`. -/
theorem lemma_2_7 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : IsReflexive X) (f g : X → EReal) (hf : TensorAHPE.IsProperClosedConvex f)
    (hg : TensorAHPE.IsProperClosedConvex g)
    (hq : (0 : StrongDual ℝ X) ∈
      sri ({x' | RockafellarMaxMono.Shared.conj f x' ≠ ⊤} -
        {x' | RockafellarMaxMono.Shared.conj g x' ≠ ⊤})) :
    parSum (RockafellarMaxMono.Shared.subdiff f) (RockafellarMaxMono.Shared.subdiff g) =
      RockafellarMaxMono.Shared.subdiff (infConv f g) := by sorry

end PertComp
