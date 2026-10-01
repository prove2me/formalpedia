-- Prove2me | Theorems.Thm_SteinitzExchange_LocalSupermod_localization_eq_min_argmax
-- name    : SteinitzExchange.LocalSupermod.localization_eq_min_argmax
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:51:27.204559+00:00
-- url     : https://prove2.me/theorems/3e6deba3-0c27-4745-941e-7a4c7b01bf5f
-- title:
--   Eq. (5.12) — the localization of ω° at p₀ is the minimum of ⟨p, x⟩ over argmax(ω[−p₀])
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a finite integral base set, $\omega:B\to\mathbb R$, and $p_0,p\in\mathbb R^V$. The localization of the concave conjugate $\omega^\circ$ at $p_0$, defined through the subdifferential $\partial\omega^\circ(p_0)$, satisfies
--
--   $$\hat L(\omega^\circ,p_0)(p)=\min\{\langle p,x\rangle\mid x\in\operatorname{argmax}(\omega[-p_0])\},$$
--
--   the minimum being attained.
--
--   This identity reduces the localization of $\omega^\circ$ to the support function $\psi^\circ$ of the maximizer set $\operatorname{argmax}(\omega[-p_0])$, which is the bridge between the Local Supermodularity Theorem and Theorems 4.4 and 5.1.
--
--   **Formalization Note.** The identity is stated as `IsLeast`: $\hat L(\omega^\circ,p_0)(p)$ is a value $\langle p,x\rangle$ at some maximizer $x$ and is at most every such value. This excludes the junk value of the real `sInf` in the definition of the localization. Note the sign: $\omega[-p_0](x)=\omega(x)-\langle p_0,x\rangle$.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 292, Eq. (5.12) (proof of Theorem 5.3)

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange
import Definitions.Def_SteinitzExchange_LocalSupermod_Localization

namespace SteinitzExchange.LocalSupermod

/-- Murota 1996, p. 292, Eq. (5.12). For `ω` on a finite integral base set `B`, every `p₀`
and every `p`, the localization `L̂(ω°, p₀)(p)` (defined by (5.8)–(5.9)) is the minimum of
`⟨p, x⟩` over `x ∈ argmax(ω[−p₀])`: it is attained there and is a lower bound. -/
theorem localization_eq_min_argmax {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) (p₀ p : V → ℝ) :
    IsLeast ((fun x => pairing p (toReal x)) '' (argmaxB B (perturb ω (-p₀)) : Set (V → ℤ)))
      (localization (concaveConj B ω) p₀ p) := by sorry

end SteinitzExchange.LocalSupermod
