-- Prove2me | Theorems.Thm_TeschlODE_Horseshoe_tentSet_isCantorSet
-- name    : TeschlODE.Horseshoe.tentSet_isCantorSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T06:14:53.004914+00:00
-- url     : https://prove2.me/theorems/95d02e90-bb8b-4c82-a005-ef61bacb7bb6
-- title:
--   Lemma 11.4 — for $\mu > 2$ the invariant set $\Lambda(T_\mu)$ of the tent map is a Cantor set
-- statement:
--   Let $\mu > 2$ and let $\Lambda(T_\mu) = \{x \in \mathbb{R} : T_\mu^n(x) \in [0,1] \ \forall n \ge 0\}$ be the set of points whose orbit under the tent map $T_\mu(x) = \frac{\mu}{2}(1 - |2x-1|)$ never leaves $[0,1]$. Then
--   $$\Lambda(T_\mu) \text{ is a Cantor set:}$$
--   it is compact, perfect and totally disconnected. In the horseshoe the lemma is used twice: once for $\Lambda(T_\mu)$ and once for $\Lambda(T_{1/\lambda})$, the two factors of $\Lambda$.
--
--   **Formalization Note.** $\mu > 2$ is the standing assumption of §11.4. At $\mu = 2$ the set is $[0,1]$, which is not a Cantor set.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 299, Lemma 11.4

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentRepellor
import Definitions.Def_TeschlODE_Horseshoe_IsCantorSet

namespace TeschlODE.Horseshoe

/-- Teschl, Lemma 11.4, p. 299: for the tent map `T_µ` with `µ > 2` (the standing assumption of
§11.4), the set `Λ(T_µ)` (11.18) of points staying in `[0, 1]` under all iterations is a Cantor
set: compact, totally disconnected and perfect. -/
theorem tentSet_isCantorSet (μ : ℝ) (hμ : 2 < μ) :
    IsCantorSet (TeschlODE.Shared.tentRepellor μ) := by sorry

end TeschlODE.Horseshoe
