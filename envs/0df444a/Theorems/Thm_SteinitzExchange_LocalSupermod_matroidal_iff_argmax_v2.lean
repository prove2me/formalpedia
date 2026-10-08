-- Prove2me | Theorems.Thm_SteinitzExchange_LocalSupermod_matroidal_iff_argmax_v2
-- name    : SteinitzExchange.LocalSupermod.matroidal_iff_argmax_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:06.804244+00:00
-- url     : https://prove2.me/theorems/1ab934fb-4485-46aa-b9c0-69a11b286ac2
-- title:
--   Theorem 5.1 at the argmax set — for a hole-free argmax set, the localisation of $\omega^\circ$ at $p_0$ is matroidal iff $\operatorname{argmax}(\omega[-p_0])$ is an integral base set
-- statement:
--   Murota 1996, p. 291, Theorem 5.1, applied at the argmax set of the localisation's subgradient functional. Let $B\subseteq\mathbb Z^V$ be a finite integral base set, $\omega:\mathbb Z^V\to\mathbb R$ (only its values on $B$ matter), and $p_0\in\mathbb R^V$. Write $\omega[-p_0](x)=\omega(x)-\langle p_0,x\rangle$ and $A_{p_0}=\operatorname{argmax}(\omega[-p_0])=\{x\in B\mid\omega(x)-\langle p_0,x\rangle\ge\omega(y)-\langle p_0,y\rangle\ \forall y\in B\}$, and assume that $A_{p_0}$ is hole-free: every integer point of its convex hull belongs to it, $A_{p_0}=\mathbb Z^V\cap\overline{A_{p_0}}$. Then the localisation $\hat L(\omega^\circ,p_0)(p)=\inf\{\langle p,b\rangle\mid b\in\partial\omega^\circ(p_0)\}$ of the concave conjugate $\omega^\circ$ at $p_0$ is *matroidal* — positively homogeneous and satisfying (C1) supermodularity and (C2) greediness — if and only if $A_{p_0}$ is a finite integral base set.
--
--   The two ingredients are visible in Murota's proof. First, Eq. (5.12) identifies the localisation pointwise with the support function of $A_{p_0}$, $\min\{\langle p,x\rangle\mid x\in A_{p_0}\}$ (`localization_eq_min_argmax`). Second, Theorem 5.1 (`baseSet_iff_support_matroidal`) turns (B1) for a hole-free finite set into matroidalness of its support function. This is the step that transports Theorem 5.1 to the conjugate: in the proof of Theorem 5.3 the hole-freeness of $A_{p_0}$ is supplied by Lemma 4.3 when $\omega$ satisfies (EXC), and by the concave-closure clause $\omega=\hat\omega$ on $B$ in the converse direction (`exc_iff_localization_matroidal`).
--
--   **Formalization Note.** The retired version quantified over every $\omega$ with no hypothesis on the argmax set; for $B=\{(2,0),(1,1),(0,2)\}$ and $\omega=(0,-1,0)$ the argmax set $\{(2,0),(0,2)\}$ has a hole, its support function $\min(2p_0,2p_1)$ is matroidal, but the set violates (B1) (accepted disproof). The new statement adds exactly the hypothesis that Theorem 5.1 places on the set whose support function it examines, hole-freeness of $A_{p_0}$ (`hconv`, the same binder as in `baseSet_iff_support_matroidal`); nothing else changes. This is strictly stronger than assuming (EXC) for $\omega$ — Lemma 4.3 derives hole-freeness of every $\operatorname{argmax}(\omega[-p])$ from (EXC) — and, unlike the (EXC) version (under which both sides hold by `exc_iff_argmax_isIntegralBaseSet` and the equivalence carries no information), it is usable in the "if" direction of the corrected Theorem 5.3, where (EXC) is the conclusion. `hull` is the convex hull in $\mathbb R^V$ of the embedded finite set; `argmaxB` is a `Finset`, nonempty because $B$ is.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), pp. 291–292, Theorem 5.1 applied at argmax(ω[−p₀]) together with Eq. (5.12); the hole-freeness hypothesis of Theorem 5.1 on the argmax set is stated explicitly (it follows from Lemma 4.3 under (EXC), p. 285)

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal
import Definitions.Def_SteinitzExchange_LocalSupermod_Localization

namespace SteinitzExchange.LocalSupermod

/-- Murota 1996, p. 291, Theorem 5.1, instantiated at the argmax set of the localisation's
subgradient functional. Let `B` be a finite integral base set, `ω : B → ℝ`, `p₀ ∈ ℝ^V`, and
suppose the argmax set `A = argmax(ω[−p₀])` of `ω[−p₀] = ω − ⟨p₀, ·⟩` over `B` is hole-free,
`A = ℤ^V ∩ conv(A)` — the hypothesis Theorem 5.1 places on the set whose support function it
examines. Then the localisation `L̂(ω°, p₀)` of the concave conjugate at `p₀` is "matroidal"
(positively homogeneous, (C1) and (C2)) if and only if `A` is a finite integral base set.

By Eq. (5.12) the localisation agrees pointwise with the support function
`ψ°(p) = min{⟨p, x⟩ | x ∈ A}` of `A`, so this is Theorem 5.1 for `A`. In the proof of
Theorem 5.3 the hole-freeness of `A` comes from Lemma 4.3 when `ω` satisfies (EXC), and from the
concave-closure clause `ω = ω̂` on `B` in the converse direction.

Corrected version: the retired statement quantified over every `ω` with no hypothesis on the
argmax set; then the argmax set may have holes, its convex hull can be an integral base polytope
(so the localisation is matroidal) while the argmax set itself violates (B1). -/
theorem matroidal_iff_argmax_v2 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) (p₀ : V → ℝ)
    (hconv : ∀ z : V → ℤ, toReal z ∈ hull (argmaxB B (perturb ω (-p₀))) →
      z ∈ argmaxB B (perturb ω (-p₀))) :
    IsMatroidal (localization (concaveConj B ω) p₀) ↔
      IsIntegralBaseSet (argmaxB B (perturb ω (-p₀))) := by sorry

end SteinitzExchange.LocalSupermod
