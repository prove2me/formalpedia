-- Prove2me | Theorems.Thm_SATotalCoeffLB_Supplement_theorem_4
-- name    : SATotalCoeffLB.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:27:49.736199+00:00
-- url     : https://prove2.me/theorems/2b85306f-0b2a-42fb-9a5e-ee62637d55c4
-- title:
--   Theorem 4 — rounding a $(k,\delta)$-non-signaling family to an exact one within $2^{2k+2}\delta$
-- statement:
--   Let $U$ be a finite set, let $k$ be a positive integer and $\delta \ge 0$ a real number, and let $\{D_S\}_{S \subseteq U,\, |S| \le k}$ be a $(k, \delta)$-non-signaling family of distributions over $\{0,1\}^S$. Then there exists an **exact** family $\{D'_S\}_{S \subseteq U,\, |S| \le k}$, that is, a $(k, 0)$-non-signaling family, such that for every $S \subseteq U$ with $|S| \le k$,
--
--   $$
--   \mathrm{SD}\bigl(D_S, D'_S\bigr) \le 2^{2k+2}\,\delta .
--   $$
--
--   Via the standard identification between $\{0,1\}$ and $\{\pm1\}$, the same conclusion holds for distributions supported on $\{\pm1\}^S$.
--
--   The theorem lets one replace an approximately consistent family of local views by an exactly consistent one, at an additive loss in each local distribution; in the paper it turns a $(k,\delta)$-non-signaling strategy into an exact one before analysing soundness. It is the paper's version of a lemma of Chiesa, Manohar and Shinkar, with the paper's non-signaling hypothesis and bound.
--
--   **Formalization Note** Both clauses are stated at once for an arbitrary alphabet $A$ with exactly two elements. Distributions are `PMF`s, statistical distance $\tfrac12\sum|\cdot|$ is the published `SamplingAC0.tvDist`, and "exact" is `IsNonSignaling k 0`.
--
--   Differences from the source:
--   - encoding: distributions over $\{0,1\}^S$, and separately over $\{\pm1\}^S$ → one statement for every alphabet $A$ with $|A| = 2$; reason: the paper's second clause is "via the standard identification", and every two-element alphabet ($\{0,1\}$, $\{\pm1\}$) is such an $A$, so no instance is added or lost.
--   - encoding: a distribution, statistical distance, marginal → Mathlib `PMF`, $\tfrac12\sum_x|p(x)-q(x)|$ on real masses, push-forward along restriction; reason: Lean convention, same objects on finite sets.
--   - encoding: an exact family → `IsNonSignaling k 0`; reason: this is the paper's definition of exact ($(k,0)$-non-signaling).
--   - encoding: a finite set $U$ and the alphabet → types `U A : Type` in the lowest universe; reason: every finite set has a copy there, and the statement is invariant under bijections.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Theorem 4, p.26 (definitions §4.2, p.25)

import Mathlib
import Definitions.Def_SATotalCoeffLB_Supplement_IsNonSignaling

namespace SATotalCoeffLB.Supplement

/-- **Theorem 4 (Rounding to exact non-signaling, [CMS20, Lemma C.3])**, p.26, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).
Let `U` be a finite set, `k` a positive integer and `δ ≥ 0`, and let `{D_S}_{S ⊆ U, |S| ≤ k}`
be a `(k, δ)`-non-signaling family of distributions on `{0,1}^S`. Then there is an exact family
`{D'_S}` with `SD(D_S, D'_S) ≤ 2^{2k+2} δ` for every `S ⊆ U` with `|S| ≤ k`; the same holds for
distributions on `{±1}^S`.

**Formalization Note** Both clauses are stated at once for an arbitrary two-element alphabet `A`
(`Fintype.card A = 2`): `Bool` gives `{0,1}^S`, a two-element type of signs gives `{±1}^S`.
Exact means `IsNonSignaling k 0`; `SD` is the published `SamplingAC0.tvDist`. -/
theorem theorem_4 {U A : Type} [Fintype U] [DecidableEq U] [Fintype A]
    (hA : Fintype.card A = 2) (k : ℕ) (hk : 0 < k) (δ : ℝ) (hδ : 0 ≤ δ)
    (D : LocalFamily U A k) (hD : IsNonSignaling k δ D) :
    ∃ D' : LocalFamily U A k, IsNonSignaling k 0 D' ∧
      ∀ (S : Finset U) (hS : S.card ≤ k), SamplingAC0.tvDist (D S hS) (D' S hS) ≤ 2 ^ (2 * k + 2) * δ := by sorry

end SATotalCoeffLB.Supplement
