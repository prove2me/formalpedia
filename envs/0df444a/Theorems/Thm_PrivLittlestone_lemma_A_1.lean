-- Prove2me | Theorems.Thm_PrivLittlestone_lemma_A_1
-- name    : PrivLittlestone.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:35:39.387055+00:00
-- url     : https://prove2.me/theorems/24ef1276-9712-4802-bc6e-02c2dd4899ed
-- title:
--   Lemma A.1 — public witnesses: $|A_h| \le d - r$, $\mathrm{LDim}(H[h,A_h]) = r$ and $W_h \cap F_r = \{h\}$
-- statement:
--   Fix a nonempty class $H \subseteq \{0,1\}^X$ with $\mathrm{LDim}(H) = d \ge 1$, its locally realizable universe $U$, rank layers $F_s$ and ranks $\rho$. For each $h \in U$ of rank $r$ there is a finite set $A_h \subseteq X$ with
--   $$
--   |A_h| \le d - r \qquad\text{and}\qquad \mathrm{LDim}(H[h, A_h]) = r
--   $$
--   such that, with $W_h = \{f \in U : f|_{A_h} = h|_{A_h}\}$,
--   $$
--   W_h \cap F_r = \{h\}.
--   $$
--   Thus every other member of $W_h$ has rank strictly below $r$.
--
--   The witnesses make descending-rank selection well defined and give the rank-increasing neighbor maps of the Littlestone candidate system.
--
--   Differences from the source:
--
--   - encoding: LDim(H[h, A_h]) = r → H[h, A_h] nonempty and ldim(H[h, A_h]) = r; reason: the paper's convention LDim(∅) = −1; the published ldim takes the value 0 on ∅
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma A.1, p.17

import Mathlib
import Definitions.Def_PrivLittlestone_rankOf

namespace PrivLittlestone

/-- **Lemma A.1 (Public witnesses; [MY26], Lemma 6)** (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), Appendix A.2.1, Lemma A.1, p.17). Fix a nonempty class `H` with
`LDim(H) = d ≥ 1`. For each `h ∈ U` of rank `r`, there is a finite set `A_h ⊆ X` with
`|A_h| ≤ d − r` and `LDim(H[h, A_h]) = r` such that, on defining `W_h = {f ∈ U : f|_{A_h} = h|_{A_h}}`,
one has `W_h ∩ F_r = {h}`. Thus every other member of `W_h` has rank strictly below `r`.

**Formalization Note** `LDim(H[h, A_h]) = r` is stated with `H[h, A_h]` nonempty (the paper's
`LDim(∅) = −1` convention; in `ℕ∞` the published `ldim ∅ = 0`). -/
theorem lemma_A_1 {X : Type*} (H : Set (X → Bool)) (d : ℕ) (hH : H.Nonempty)
    (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d) :
    ∀ h ∈ localUniverse H d, ∃ A : Finset X,
      A.card ≤ d - rankOf H d h ∧ (restrictCls H h A).Nonempty ∧
      UnderstandingML.ldim (restrictCls H h A) = (rankOf H d h : ℕ∞) ∧
      {f ∈ localUniverse H d | ∀ x ∈ A, f x = h x} ∩ rankLayer H d (rankOf H d h) = {h} ∧
      ∀ f ∈ localUniverse H d, (∀ x ∈ A, f x = h x) → f ≠ h → rankOf H d f < rankOf H d h := by sorry

end PrivLittlestone
