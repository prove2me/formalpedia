-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_exc_iff_exc_loc
-- name    : SteinitzExchange.Extension.exc_iff_exc_loc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:42:26.602769+00:00
-- url     : https://prove2.me/theorems/126c3710-b2c3-413a-83f8-db21f1fac230
-- title:
--   Theorem 3.1 — (EXC) is equivalent to the local exchange property (EXC$_{\mathrm{loc}}$)
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a finite integral base set and $\omega:B\to\mathbb R$. Then
--
--   $$\omega\ \text{satisfies (EXC)}\iff\omega\ \text{satisfies (EXC}_{\mathrm{loc}}).$$
--
--   Thus the exchange inequality need only be checked for pairs $x,y\in B$ with $\|x-y\|=4$, and only for one exchange pair $(u,v)$; this parallels the characterization of concavity by a local (second-order) condition. It is the tool used to prove the "if" direction of Theorem 4.4.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 282, Theorem 3.1

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 282, Theorem 3.1: on a finite integral base set, (EXC) ⇔ (EXC_loc). -/
theorem exc_iff_exc_loc {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔ SatisfiesEXCLoc B ω := by sorry

end SteinitzExchange.Extension
