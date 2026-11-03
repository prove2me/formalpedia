-- Prove2me | Theorems.Thm_PertComp_lemma_2_11_i
-- name    : PertComp.lemma_2_11_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:38.616496+00:00
-- url     : https://prove2.me/theorems/c3224382-0fd8-4633-81d4-b15b98468c41
-- title:
--   Lemma 2.11(i): $(-\mathscr L_\Phi(x,\cdot))^*=\Phi(x,\cdot)$
-- statement:
--   Let $X$ and $U$ be reflexive real Banach spaces, let $\phi\in\Gamma_0(X)$, and let $\Phi\in\Gamma_0(X\oplus U)$ be a perturbation of $\phi$, i.e. $\phi(x)=\Phi(x,0)$ for every $x$. Then for every $x\in X$,
--   $$\big(-\mathscr L_\Phi(x,\cdot)\big)^*=\Phi(x,\cdot),$$
--   where $\mathscr L_\Phi$ is the Lagrangian (2.24) and the conjugate of the function $-\mathscr L_\Phi(x,\cdot)$ on $U^*$ is read on $U^{**}=U$.
--
--   Differences from the source:
--   - encoding: functions with values in ]−∞, +∞] or [−∞, +∞] → EReal-valued functions; a function of Γ₀ never takes ⊥; reason: Lean convention; same instances
--   - encoding: reflexive real Banach space → NormedSpace ℝ with [CompleteSpace] and IsReflexive (the canonical map into the bidual is onto); reason: Mathlib has no reflexivity class; same spaces
--   - encoding: X ⊕ U with the Euclidean product norm (2.2) → Lean product X × U (sup norm); reason: equivalent norms: same topology, same pairing (2.1)
--   - encoding: (−𝓛_Φ(x, ·))*, a function on U** = U → the conjugate on StrongDual ℝ (StrongDual ℝ U) evaluated at the canonical image of u; reason: reflexivity identifies U** with U
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Lemma 2.11(i), p.9

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Conj
import Definitions.Def_PertComp_IsReflexive
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PertComp_lag

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Lemma 2.11(i)**, p.9: let `X` and `U` be
reflexive real Banach spaces, `ϕ ∈ Γ₀(X)`, and `Φ ∈ Γ₀(X ⊕ U)` a perturbation of `ϕ`
(`ϕ(x) = Φ(x, 0)` for every `x`). Then for every `x ∈ X`, `(−𝓛_Φ(x, ·))* = Φ(x, ·)`.

**Formalization Note.** `−𝓛_Φ(x, ·)` is a function on `U*`, so its conjugate is a function on
`U**`; the identity is stated on `U` through the canonical embedding
`NormedSpace.inclusionInDoubleDual ℝ U`, which is onto by reflexivity. -/
theorem lemma_2_11_i {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (hX : IsReflexive X) (hU : IsReflexive U) (ϕ : X → EReal)
    (hϕ : TensorAHPE.IsProperClosedConvex ϕ)
    (Φ : X × U → EReal) (hΦ : TensorAHPE.IsProperClosedConvex Φ) (hpert : ∀ x : X, ϕ x = Φ (x, 0))
    (x : X) (u : U) :
    RockafellarMaxMono.Shared.conj (fun u' : StrongDual ℝ U => -lag Φ x u')
        (NormedSpace.inclusionInDoubleDual ℝ U u) = Φ (x, u) := by sorry

end PertComp
