-- Prove2me | Theorems.Thm_VolunteerNotify_lemma_3
-- name    : VolunteerNotify.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:38:37.400234+00:00
-- url     : https://prove2.me/theorems/83fbfea1-892d-4df7-ad86-1bcb12f440cf
-- title:
--   Lemma 3 — $J_{v,1}\ge\frac1{2-q}f_v(x)$ for $x\in\mathcal P$
-- statement:
--   Let $q$ be the MDHR of $g$. For any $x\in\mathcal P$ and volunteer $v$, if $(\tilde x,J)$ solves (6)–(8) for the input $x$, then
--   $$
--   J_{v,1}\ge\frac1{2-q}f_v(x).
--   $$
--   This compares the value of the dynamic program to the always-active contribution of $v$, and carries the online loss of the policy.
--
--   Differences from the source:
--   - reading: Lemma 3 says "for any x ∈ P" while J is defined from x* (p.16) → J is built from the same x; reason: the proof on p.20 works with one vector; with J from a fixed x* and x arbitrary the claim is false (V = 2, S = T = 1, λ = p = 1, g(1) = 1, x* = (1, 0), x = (0, 1)); x = x* is the use on p.21
--   - generalization: q is the minimum over τ ∈ ℕ of the hazard rates (Definition 1) → q is their infimum (`mdhr`); reason: the minimum need not exist, e.g. hazards 1/2 + 1/(τ+2); the infimum equals the minimum whenever it exists, so the statement specializes to the source
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1, a = 0 allowed; reason: Lean convention; at a = 0 the sums are empty and no instance of the source changes
--   - encoding: (6)–(8), computed by Algorithm 1, with an s = 0 term in (8) → `IsDP`, a hypothesis on (x̃, J) listing the equations, with the s = 0 term written λ_{0,t} J_{v,t+1}; reason: the equations have exactly one solution; variables of type 0 are 0 (fn. 18, p.16)
--   - encoding: Z > 0 with law g, τ ∈ ℕ → `g : ℕ → ℝ` with `g 0 = 0`, τ ranges over positive integers; reason: ℕ is {1, 2, …} in the source; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Lemma 3, p.19

import Mathlib
import Definitions.Def_VolunteerNotify_lpValue
import Definitions.Def_VolunteerNotify_f
import Definitions.Def_VolunteerNotify_IsDP

namespace VolunteerNotify

/-- Lemma 3, Manshadi–Rodilitz, arXiv:2002.08474v7, p.19: for any `x ∈ P` and volunteer `v`,
`J_{v,1} ≥ (1/(2 − q)) f_v(x)`.

**Formalization Note.** `J` is built from the same `x`, as in the proof on p.20; with `J` built
from a fixed `x*` and `x` arbitrary the inequality is false. -/
theorem lemma_3 {V S T : ℕ} (I : Instance V S T) (x xt : Decision V S T)
    (J : Fin V → Fin (T + 1) → ℝ) (hx : x ∈ feasibleSet I) (hdp : IsDP I x xt J) (v : Fin V) :
    1 / (2 - mdhr I.g) * fv I x v ≤ J v 0 := by sorry

end VolunteerNotify
