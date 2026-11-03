-- Prove2me | Theorems.Thm_PertComp_lemma_2_5_ii
-- name    : PertComp.lemma_2_5_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:35.138012+00:00
-- url     : https://prove2.me/theorems/1a27b315-ebce-410b-8dc9-f06249d89333
-- title:
--   Lemma 2.5(ii): $(\partial f)^{-1}=\partial f^*$
-- statement:
--   Let $X$ be a reflexive real Banach space and $f\in\Gamma_0(X)$. Then $(\partial f)^{-1}=\partial f^*$: for every $x\in X$ and $x^*\in X^*$,
--   $$x^*\in\partial f(x)\iff x\in\partial f^*(x^*),$$
--   where $\partial f^*(x^*)\subset X^{**}=X$.
--
--   Differences from the source:
--   - encoding: functions with values in ]−∞, +∞] or [−∞, +∞] → EReal-valued functions; a function of Γ₀ never takes ⊥; reason: Lean convention; same instances
--   - encoding: reflexive real Banach space → NormedSpace ℝ with [CompleteSpace] and IsReflexive (the canonical map into the bidual is onto); reason: Mathlib has no reflexivity class; same spaces
--   - encoding: subgradients of a function on a dual space V* lie in V** = V → subdiffPre: the points of V whose canonical image in V** is a subgradient; reason: reflexivity identifies V** with V; same sets
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Lemma 2.5(ii), p.6 (citing Zălinescu [57, Theorem 2.4.4(iv)])

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Conj
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_PertComp_IsReflexive
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PertComp_subdiffPre

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Lemma 2.5(ii)**, p.6: let `X` be a reflexive
real Banach space and `f ∈ Γ₀(X)`. Then `(∂f)⁻¹ = ∂f*`.

**Formalization Note.** As an equality of graphs: `x* ∈ ∂f(x)` iff `x ∈ ∂f*(x*)`, where
`∂f*(x*) ⊂ X** = X` is `subdiffPre (conj f) x*`. -/
theorem lemma_2_5_ii {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : IsReflexive X) (f : X → EReal) (hf : TensorAHPE.IsProperClosedConvex f) (x : X)
    (x' : StrongDual ℝ X) :
    x' ∈ RockafellarMaxMono.Shared.subdiff f x ↔
      x ∈ subdiffPre (RockafellarMaxMono.Shared.conj f) x' := by sorry

end PertComp
