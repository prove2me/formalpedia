-- Prove2me | Theorems.Thm_VolDisclosure_Evidence_lemma_A_1
-- name    : VolDisclosure.Evidence.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:00.724667+00:00
-- url     : https://prove2.me/theorems/f140b563-005c-4107-9bd4-61eb0c03e98d
-- title:
--   Lemma A.1, p. 38 — T maps F1, the functions in F equal to s* from (1+r)pδ/r on, into itself
-- statement:
--   Fix parameters satisfying the standing assumptions of §3 and an evidence probability $\pi \in [0,1)$. Let $\mathcal F$ be the class of continuous functions $q$ on $\mathbb R_+$ with $0 \le q \le s^*$, and
--   $$
--   \mathcal F_1 = \Big\{q \in \mathcal F : q(v) = s^* \text{ for all } v \ge \frac{(1+r)p\delta}{r}\Big\}.
--   $$
--   If $q \in \mathcal F_1$, then $Tq \in \mathcal F_1$: the Bellman operator (T) maps $\mathcal F_1$ into itself.
--
--   Together with the contraction property of $T$, this pins the fixed point of $T$ to first-best value from $\bar v = (1+r)p\delta/r$ on.
--
--   **Formalization Note.** The conclusion includes $Tq \in \mathcal F$ (continuity on $\mathbb R_+$ and $0 \le Tq \le s^*$), which the paper asserts on p. 37 ("$T : \mathcal F \to \mathcal F$ is well defined") and which is part of "$Tq \in \mathcal F_1$". The range $\pi \in [0,1)$ covers both the problem with evidence and the no-evidence benchmark $\pi = 0$, which the paper treats with the same program (p. 14).
-- source:
--   Fu & Trigilia, Voluntary Disclosure, Moral Hazard and Default Risk, working paper (August 28, 2019), p. 38, Lemma A.1 (with p. 37, (T))

import Mathlib
import Definitions.Def_VolDisclosure_Evidence_Model

namespace VolDisclosure.Evidence

/-- Lemma A.1 (p. 38): if `q ∈ F` equals `s*` from `(1+r)pδ/r` on, so does `Tq`. -/
theorem lemma_A_1 (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π < 1)
    (q : ℝ → ℝ) (hq : InF P q) (hq1 : ∀ v, P.vBar ≤ v → q v = P.sStar) :
    InF P (T P π q) ∧ ∀ v, P.vBar ≤ v → T P π q v = P.sStar := by sorry

end VolDisclosure.Evidence
