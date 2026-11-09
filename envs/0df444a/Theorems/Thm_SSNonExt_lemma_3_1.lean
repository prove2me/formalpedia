-- Prove2me | Theorems.Thm_SSNonExt_lemma_3_1
-- name    : SSNonExt.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:54:50.147092+00:00
-- url     : https://prove2.me/theorems/5ca2c3a5-cedc-4908-974e-2f65bb31ef44
-- title:
--   Lemma 3.1 — correctness of $\Pi_b$: $\mathrm{Rec}(F(m,k),G(m,k))=m$
-- statement:
--   Let $b\ge2$, $V=\mathbb F_{2^b}$ and $\alpha\in V\setminus\{0,1\}$, and let $F,G$ be the shares of the scheme $\Pi_b$ (table (1)) and $\mathrm{Rec}$ the tag-reading reconstruction map. Then
--
--   $$\mathrm{Rec}\big(F(m,k),G(m,k)\big)=m\qquad\text{for all }m\in V,\ k\in\mathcal K=\{L,R,C\}\times V.$$
--
--   This is the correctness half of the main theorem on the three-branch key set.
--
--   Differences from the source:
--   - generalization: there is a map Rec with Rec(F(m,k), G(m,k)) = m → the explicit Rec of the proof of Lemma 3.1 satisfies it; reason: an explicit witness implies the existence claim
--   - encoding: keys {L,R,C} × V, shares {0,1} × V with x = (0,x), x̄ = (1,x) → Branch × GaloisField 2 b and Bool × GaloisField 2 b with false = untagged, true = tagged; reason: the same sets; the bar stays a formal tag
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), Lemma 3.1 and its proof, p.6 (PDF p.6)

import Mathlib
import Definitions.Def_SSNonExt_scheme

namespace SSNonExt

/-- **Lemma 3.1 (Correctness).** "There is a map Rec with Rec(F(m, k), G(m, k)) = m for all m ∈ V and
k ∈ 𝒦."
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), Lemma 3.1 and its proof, p.6 (PDF p.6).

Standing hypotheses of §3 (p.6): `b ≥ 2`, `α ∈ 𝔽_{2^b} \ {0, 1}`.

**Formalization Note.** The map is the explicit `rec` of the proof of Lemma 3.1 (tags identify the
branch), which implies the existential "there is a map Rec". -/
theorem lemma_3_1 (b : ℕ) (hb : 2 ≤ b) (α : V b) (hα0 : α ≠ 0) (hα1 : α ≠ 1) :
    ∀ (m : V b) (k : Key b), rec α (F m k) (G α m k) = m := by sorry

end SSNonExt
