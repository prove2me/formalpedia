-- Prove2me | Theorems.Thm_SteinitzExchange_LocalSupermod_exc_iff_localization_matroidal
-- name    : SteinitzExchange.LocalSupermod.exc_iff_localization_matroidal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:52:48.191985+00:00
-- url     : https://prove2.me/theorems/ea5a1cbc-c4c8-455d-851b-843197538908
-- title:
--   Theorem 5.3 (Local Supermodularity Theorem, corrected) — (EXC) iff ω = ω̂ on B and every localization of ω° is "matroidal"
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a finite integral base set and $\omega:B\to\mathbb R$. Let $\omega^\circ(p)=\min\{\langle p,x\rangle-\omega(x)\mid x\in B\}$ be the concave conjugate, $\hat\omega$ the concave closure, and $\hat L(\omega^\circ,p_0)(p)=\inf\{\langle p,b\rangle\mid b\in\partial\omega^\circ(p_0)\}$ the localization of $\omega^\circ$ at $p_0$. Then $\omega$ satisfies (EXC) if and only if
--
--   1. $\omega(x)=\hat\omega(x)$ for every $x\in B$, and
--   2. $\hat L(\omega^\circ,p_0)$ is "matroidal" (satisfies (C1) and (C2)) at every point $p_0\in\mathbb R^V$.
--
--   In short,
--
--   $$\omega\ \text{is M-concave}\iff\omega=\hat\omega\ \text{on}\ B\ \text{and}\ \omega^\circ\ \text{is "locally matroidal" everywhere}.$$
--
--   Since (C1) is a supermodularity condition, the theorem says that the exchange property (EXC) is "a collection of local supermodularity" of the conjugate, just as (B1) for a set corresponds to supermodularity of its support function (Theorem 5.1).
--
--   **Formalization Note.** The paper's statement has only condition 2. The "only if" direction holds as printed, but the "if" direction fails without condition 1: see `localization_matroidal_not_sufficient`, where $B=\{(2,0),(1,1),(0,2)\}$ and $\omega=(0,-10,0)$. The paper's proof applies Theorem 5.1 to $\operatorname{argmax}(\omega[-p_0])$, which requires every integer point of its convex hull to be a maximizer; condition 1 (ω extends to a concave function, which the paper proves for M-concave ω in Section 4) supplies this. The localization is defined by (5.8)–(5.9), not by formula (5.12). "Matroidal" includes positive homogeneity, and (C2) is required for every non-increasing indexing of $V$.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 292, Theorem 5.3 (corrected by the concave-closure condition; concave closure from p. 284, Eq. (4.2))

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal
import Definitions.Def_SteinitzExchange_LocalSupermod_Localization

namespace SteinitzExchange.LocalSupermod

/-- Murota 1996, p. 292, Theorem 5.3 (Local Supermodularity Theorem), corrected. For `ω` on a
finite integral base set `B`: `ω` satisfies (EXC) iff `ω` coincides on `B` with its concave
closure `ω̂` (4.2) and the localization `L̂(ω°, p₀)` of the concave conjugate `ω°` (5.6) at
`p₀` ((5.8)–(5.9)) is "matroidal" at every `p₀ ∈ ℝ^V`. The printed statement omits the
concave-closure clause; without it the "if" direction fails
(see `localization_matroidal_not_sufficient`). -/
theorem exc_iff_localization_matroidal {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔
      ((∀ x ∈ B, concaveClosure B ω (toReal x) = ω x) ∧
        ∀ p₀ : V → ℝ, IsMatroidal (localization (concaveConj B ω) p₀)) := by sorry

end SteinitzExchange.LocalSupermod
