-- Prove2me | Theorems.Thm_UnionVolEst_claim_9
-- name    : UnionVolEst.claim_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:05:41.886191+00:00
-- url     : https://prove2.me/theorems/60d33165-443b-492d-bda3-bdb79b955f4d
-- title:
--   Claim 9 — $(1-\varepsilon/32)F_0\le F_0'\le F_0$, and $(1\pm15\varepsilon/16)F_0'\subseteq(1\pm\varepsilon)F_0$ (corrected: $1-\beta\to1-M\beta$)
-- statement:
--   Let $K_1,\dots,K_M\subseteq\mathbb R^n$ ($M\ge1$) be measurable sets of positive finite volume, $\varepsilon\in(0,1)$, and let $D_1,\dots,D_M$ be distributions with $D_j$ $(\varepsilon/32,\varepsilon/(32M))$-almost-$\ell_\infty$-close to the uniform distribution on $K_j$. With $F_0=\mathrm{Vol}(\bigcup_j K_j)$ and $F_0'=\sum_j\mathrm{Vol}(\hat K_j\setminus\mathrm{Bad}_j)$,
--   $$
--   \Big(1-\frac{\varepsilon}{32}\Big)F_0 \le F_0' \le F_0,
--   $$
--   and every $\mathrm{Out}$ with $|\mathrm{Out}-F_0'|\le \frac{15\varepsilon}{16}F_0'$ satisfies $|\mathrm{Out}-F_0|\le\varepsilon F_0$.
--
--   The claim reduces estimating $F_0$ to estimating the volume of the good parts.
--
--   Differences from the source:
--   - correction: (1 − β) F₀ = (1 − ε/32) F₀ ≤ F′₀ → (1 − ε/32) F₀ ≤ F′₀; reason: β = ε/(32M), so 1 − β ≠ 1 − ε/32 for M ≥ 2; the proof shows F₀ ≤ F′₀ + MβF₀ = F′₀ + (ε/32)F₀
--   - generalization: (r, R)-fat convex bodies K_1, …, K_M with geometric parameters r, R → measurable sets of positive finite volume; r, R not modelled; reason: convexity and fatness are used only to implement the oracles (Section 6); every (r, R)-fat convex body is such a set, so the statement specializes to the paper's
--   - reading: "lies in (1 ± a)x" → closed interval |y − x| ≤ a·x; reason: the page writes both open-looking and closed intervals for the same events; the closed reading is the one Claim 9 and Lemma 16 item 3 use
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Claim 9, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_UnionVolEst_IsAlmostLinftyClose
import Definitions.Def_UnionVolEst_unionVolume
import Definitions.Def_UnionVolEst_goodVolume

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace UnionVolEst

/-- Claim 9 (Equivalence of `F₀` and `F′₀`) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24)), printed p.20, PDF p.22, corrected: if every
sampling distribution `D_j` is `(ε/32, ε/(32M))`-almost-ℓ∞-close to the uniform distribution on
`K_j`, then `(1 − ε/32) F₀ ≤ F′₀ ≤ F₀`, and every `Out ∈ (1 ± 15ε/16) F′₀` lies in `(1 ± ε) F₀`.

**Formalization Note** (corrected: `(1 − β)F₀` → `(1 − Mβ)F₀ = (1 − ε/32)F₀`) The page prints
`(1 − β) F₀ = (1 − ε/32) F₀`, which is false for `M ≥ 2` since `β = ε/(32M)`; its proof gives
`F₀ ≤ F′₀ + MβF₀`, i.e. the chain from `(1 − ε/32) F₀` stated here. Intervals `(1 ± a)x` are
closed: `|Out − x| ≤ a x`. -/
theorem claim_9 {n M : ℕ} (hM : 1 ≤ M) (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ i, MeasurableSet (K i)) (hK0 : ∀ i, volume (K i) ≠ 0)
    (hKfin : ∀ i, volume (K i) ≠ ⊤)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (D : Fin M → Measure (EuclideanSpace ℝ (Fin n))) (hDprob : ∀ i, IsProbabilityMeasure (D i))
    (hD : ∀ i, IsAlmostLinftyClose (ε / 32) (ε / (32 * M)) (D i) (volume[|K i])) :
    ((1 - ε / 32) * unionVolume K ≤ goodVolume K D (ε / 32) ∧ goodVolume K D (ε / 32) ≤ unionVolume K) ∧
      ∀ Out : ℝ, |Out - goodVolume K D (ε / 32)| ≤ 15 * ε / 16 * goodVolume K D (ε / 32) →
        |Out - unionVolume K| ≤ ε * unionVolume K := by sorry

end UnionVolEst
