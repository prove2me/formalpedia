-- Prove2me | Theorems.Thm_SteinitzExchange_LocalSupermod_matroidal_iff_argmax
-- name    : SteinitzExchange.LocalSupermod.matroidal_iff_argmax
-- status  : Open
-- author  : @WillR
-- created : 2026-09-28T15:41:32.371872+00:00
-- url     : https://prove2.me/theorems/1607bd4c-3fab-4fd5-a9d2-4191b7a360b6
-- title:
--   Theorem 5.1 at the argmax set — the localisation of ω° at p₀ is matroidal iff argmax(ω[−p₀]) is an integral base set
-- statement:
--   Murota 1996, p. 291, Theorem 5.1, applied at the argmax set of the localisation's subgradient functional. Let $B \subseteq \mathbb{Z}^V$ be a finite integral base set, $\omega : \mathbb{Z}^V \to \mathbb{R}$, and $p_0 \in \mathbb{R}^V$. Write $\omega[-p_0](x) = \omega(x) - \langle p_0, x\rangle$ and $A_{p_0} = \operatorname{argmax}(\omega[-p_0]) = \{x \in B \mid \omega(x) - \langle p_0, x\rangle \ge \omega(y) - \langle p_0, y\rangle\ \forall y \in B\}$. Then the localisation $\hat{L}(\omega^\circ, p_0)(p) = \inf\{\langle p, b\rangle \mid b \in \partial\omega^\circ(p_0)\}$ of the concave conjugate $\omega^\circ$ at $p_0$ is \emph{matroidal} -- positive homogeneous and satisfying (C1) supermodularity and (C2) greediness -- if and only if $A_{p_0}$ is a finite integral base set.\n\nThe two ingredients are visible in Murota's proof. First, Eq. (5.12) identifies the localisation pointwise with the support function of $A_{p_0}$, $\min\{\langle p, x\rangle \mid x \in A_{p_0}\}$. Second, Lemma 4.3 says that every integer point of the convex hull of a maximiser set $A_{p_0}$ lies again in $A_{p_0}$, which is exactly the hypothesis that Theorem 5.1 requires of the set at which its support function is taken. Theorem 5.1 then turns (B1) for $A_{p_0}$ into matroidalness of that support function, hence of the localisation. This is the step that transports Theorem 5.1 to the conjugate and is the bridge between Eq. (5.12) and Theorem 4.4 in the proof of Theorem 5.3.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 291-292, Theorem 5.1 applied at argmax(ω[−p₀]) together with Eq. (5.12) and Lemma 4.3

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal
import Definitions.Def_SteinitzExchange_LocalSupermod_Localization

namespace SteinitzExchange.LocalSupermod

/-- Murota 1996, p. 291, Theorem 5.1, instantiated at the argmax set of the localisation's
subgradient functional. For every `p₀ : V → ℝ`, the localisation `L̂(ω°, p₀)` of the concave
conjugate at `p₀` is "matroidal" (satisfies positive homogeneity, (C1) and (C2)) if and only if the
argmax set `argmax(ω[−p₀])` of `ω[−p₀] = ω − ⟨p₀, ·⟩` over `B` is a finite integral base set.

This is the step that carries Theorem 5.1 (B1) ↔ matroidalness of the support function over to
Theorem 5.3: by Eq. (5.12) the localisation agrees pointwise with the support function
`ψ°(p) = min{⟨p, x⟩ | x ∈ argmax(ω[−p₀])}` of the argmax set, and Lemma 4.3 supplies the
integral-convexity hypothesis (`hconv`) that Theorem 5.1 requires, since every integer point of the
convex hull of a maximiser set is again a maximiser. -/
theorem matroidal_iff_argmax {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) (p₀ : V → ℝ) :
    IsMatroidal (localization (concaveConj B ω) p₀) ↔
      IsIntegralBaseSet (argmaxB B (perturb ω (-p₀))) := by sorry

end SteinitzExchange.LocalSupermod
