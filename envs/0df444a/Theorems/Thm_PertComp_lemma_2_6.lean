-- Prove2me | Theorems.Thm_PertComp_lemma_2_6
-- name    : PertComp.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:10.031627+00:00
-- url     : https://prove2.me/theorems/cf5d074e-f05c-421b-a0b8-f28ac5292dda
-- title:
--   Lemma 2.6 (Attouch–Brezis): $(f+g)^*=f^*\Box g^*\in\Gamma_0(X^*)$ and $\partial(f+g)=\partial f+\partial g$
-- statement:
--   Let $X$ be a reflexive real Banach space, let $f,g\in\Gamma_0(X)$, and suppose that $0\in\operatorname{sri}(\operatorname{dom} f-\operatorname{dom} g)$. Then:
--
--   1. $(f+g)^*=f^*\,\Box\,g^*$ and $f^*\,\Box\,g^*\in\Gamma_0(X^*)$;
--   2. $\partial(f+g)(x)=\partial f(x)+\partial g(x)$ for every $x\in X$.
--
--   These are the conjugate and subdifferential sum rules under the Attouch–Brezis qualification condition; the proof of Theorem 3.3 uses (i) for the dual objective and (ii) for the Kuhn–Tucker operator.
--
--   Differences from the source:
--   - encoding: functions with values in ]−∞, +∞] or [−∞, +∞] → EReal-valued functions; a function of Γ₀ never takes ⊥; reason: Lean convention; same instances
--   - encoding: reflexive real Banach space → NormedSpace ℝ with [CompleteSpace] and IsReflexive (the canonical map into the bidual is onto); reason: Mathlib has no reflexivity class; same spaces
--   - reading: closure (in (2.8)) and lower semicontinuity of functions on X* → for the norm topology of StrongDual ℝ X; reason: the sets and functions are convex and X is reflexive, so norm, weak and weak* closures (and lower semicontinuity) coincide
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Lemma 2.6(i)–(ii), p.7 (citing Attouch–Brezis [4, Theorem 1.1, Corollary 2.1])

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Conj
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_PertComp_IsReflexive
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PertComp_sri
import Definitions.Def_PertComp_infConv

namespace PertComp

open Pointwise

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Lemma 2.6**, p.7 (Attouch–Brezis [4]): let `X`
be a reflexive real Banach space, `f, g ∈ Γ₀(X)`, and suppose `0 ∈ sri (dom f − dom g)`. Then
(i) `(f + g)* = f* □ g* ∈ Γ₀(X*)`; (ii) `∂(f + g) = ∂f + ∂g`.

**Formalization Note.** (i) is the identity together with `f* □ g* ∈ Γ₀(X*)` (lower
semicontinuity for the norm topology of `X*`); (ii) is an identity at every point, with `+` the
pointwise sum of subsets of `X*`. -/
theorem lemma_2_6 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : IsReflexive X) (f g : X → EReal) (hf : TensorAHPE.IsProperClosedConvex f)
    (hg : TensorAHPE.IsProperClosedConvex g)
    (hq : (0 : X) ∈ sri ({x | f x ≠ ⊤} - {x | g x ≠ ⊤})) :
    (RockafellarMaxMono.Shared.conj (f + g) =
        infConv (RockafellarMaxMono.Shared.conj f) (RockafellarMaxMono.Shared.conj g) ∧
      TensorAHPE.IsProperClosedConvex
        (infConv (RockafellarMaxMono.Shared.conj f) (RockafellarMaxMono.Shared.conj g))) ∧
    ∀ x : X, RockafellarMaxMono.Shared.subdiff (f + g) x =
      RockafellarMaxMono.Shared.subdiff f x + RockafellarMaxMono.Shared.subdiff g x := by sorry

end PertComp
