-- Prove2me | Theorems.Thm_SSNonExt_lemma_3_2
-- name    : SSNonExt.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:59:04.37938+00:00
-- url     : https://prove2.me/theorems/4b6a6e55-6a9a-4848-b265-c2fe12b413e2
-- title:
--   Lemma 3.2 — privacy: each share is uniform on $V\cup\{\bar i:i\notin T\}$
-- statement:
--   Let $b\ge2$, $V=\mathbb F_{2^b}$, $\alpha\in V\setminus\{0,1\}$. For every $T\subseteq V$ and every message $m\in V$, if $K\sim P_T$ then each of $F(m,K)$ and $G(m,K)$ is uniformly distributed on
--
--   $$V\cup\{\bar i:i\notin T\}.\tag{3}$$
--
--   In particular, since (3) does not depend on $m$, the scheme $\Pi_b$ is perfectly private for $\mathcal S_b$ in the sense of Definition 2.1 (threshold $2$, $\delta=0$).
--
--   Differences from the source:
--   - encoding: F(m,K) and G(m,K) uniform on (3), K ∼ P_T → the push-forwards of P_T along F m and G α m equal PMF.uniformOfFinset of the set (3); reason: the same statement about laws
--   - encoding: perfectly private for 𝒮_b → IsPrivate 2 0 (srcClass b) (scheme α) (Definition 2.1 with t = 2, δ = 0, one share alphabet {0,1} × V); reason: both share alphabets of Π_b are {0,1} × V
--   - encoding: keys {L,R,C} × V, shares {0,1} × V with x = (0,x), x̄ = (1,x) → Branch × GaloisField 2 b and Bool × GaloisField 2 b with false = untagged, true = tagged; reason: the same sets; the bar stays a formal tag
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), Lemma 3.2, p.6 (PDF p.6)

import Mathlib
import Definitions.Def_SSNonExt_IsPrivate
import Definitions.Def_SSNonExt_sourceClass

namespace SSNonExt

/-- **Lemma 3.2 (Privacy).** "For every T ⊆ V and every m ∈ V, if K ∼ P_T then each of F(m, K) and
G(m, K) is uniform on V ∪ {ī : i ∉ T}. (3) In particular Π_b is perfectly private for 𝒮_b."
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), Lemma 3.2, p.6 (PDF p.6).

Standing hypotheses of §3 (p.6): `b ≥ 2`, `α ∈ 𝔽_{2^b} \ {0, 1}`.

**Formalization Note.** "Uniform on (3)" is equality of the push-forward `(P_T).map (F m)` (resp.
`G α m`) with `PMF.uniformOfFinset` of the set (3), `shareSupport T`. Perfect privacy is
Definition 2.1 with `t = 2`, `δ = 0` for the class `srcClass b` and the sharing map `(F, G)`. -/
theorem lemma_3_2 (b : ℕ) (hb : 2 ≤ b) (α : V b) (hα0 : α ≠ 0) (hα1 : α ≠ 1) :
    (∀ (T : Finset (V b)) (m : V b),
        (srcP T).map (F m) = PMF.uniformOfFinset (shareSupport T) (shareSupport_nonempty T) ∧
        (srcP T).map (G α m) = PMF.uniformOfFinset (shareSupport T) (shareSupport_nonempty T)) ∧
      IsPrivate 2 0 (srcClass b) (scheme α) := by sorry

end SSNonExt
