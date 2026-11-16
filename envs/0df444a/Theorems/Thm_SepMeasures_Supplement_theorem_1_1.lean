-- Prove2me | Theorems.Thm_SepMeasures_Supplement_theorem_1_1
-- name    : SepMeasures.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:15:59.049113+00:00
-- url     : https://prove2.me/theorems/53931129-0790-4852-b708-b586a2e5517a
-- title:
--   Theorem 1.1 — for every norm on $\mathbb R$, $\alpha(\mathcal P^1_f)=1/3$
-- statement:
--   Let $\|\cdot\|$ be any norm on $\mathbb R$, and let $\mathcal P^1_f$ be the family of pairs $(\mu,\nu)$ of probability measures on $\mathbb R$ with finite first moments. For such a pair let $L_{\mu,\nu}=\mathbb E\|X-Y\|$ with $X\sim\mu$, $Y\sim\nu$ independent, and for a threshold $\tau$ let $C_{\mu,\nu}(\tau)$ be the part of this expectation carried by pairs that lie strictly on opposite sides of $\tau$. The cut ratio of the family is
--   $$\alpha(\mathcal P^1_f)=\inf_{\substack{(\mu,\nu)\in\mathcal P^1_f\\ L_{\mu,\nu}>0}}\ \sup_{\tau\in\mathbb R}\frac{C_{\mu,\nu}(\tau)}{L_{\mu,\nu}} .$$
--   Then
--   $$\alpha(\mathcal P^1_f)=\frac13 .$$
--
--   So on the line some threshold always captures at least one third of the expected red–blue distance, and no constant larger than $1/3$ is guaranteed: the lower bound is Theorem 3.1, and the matching upper bound comes from a family of four-atom configurations whose best threshold captures a fraction tending to $1/3$.
--
--   **Formalization Note** $\mathbb R$ is `EuclideanSpace ℝ (Fin 1)`; a norm is a seminorm $N$ with $N(x)=0\Rightarrow x=0$. Hyperplanes of $\mathbb R$ are thresholds given by $(u\neq0,c)$ with open half-lines. The family and the cut ratio are the published `SepMeasures.Pf` and `SepMeasures.cutRatio`. Since $\mathcal P^1_f$ contains pairs with $L>0$, the infimum is over a non-empty set.
--
--   Differences from the source:
--   - encoding: a norm on ℝ → a seminorm N on EuclideanSpace ℝ (Fin 1) with N x = 0 → x = 0; reason: Lean convention for an arbitrary (non-Euclidean) norm on the Euclidean carrier; same instances
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Theorem 1.1, p.4 (lower bound Theorem 3.1, p.15; upper bound Proposition 4.1, pp.34–35)

import Mathlib
import Definitions.Def_SepMeasures_CutValue
import Definitions.Def_SepMeasures_Families

open MeasureTheory

namespace SepMeasures

namespace Supplement

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Theorem 1.1, p.4: for every norm on `ℝ`,
`α(𝒫^1_f) = 1/3`.

**Formalization Note.** `ℝ` is `EuclideanSpace ℝ (Fin 1)`; a norm on it is a `Seminorm` `N` with
`N x = 0 → x = 0`. The family is the published `𝒫^1_f` (probability measures with finite first
moments, no geometric condition); hyperplanes of `ℝ` are thresholds, separation is strict, and
`cutRatio` is the published Definition 2.1. `𝒫^1_f` contains pairs with `L > 0` (two Dirac
measures at distinct points), so the infimum is not Lean's empty-index value `0`. -/
theorem theorem_1_1 (N : Seminorm ℝ (E 1)) (hN : ∀ x, N x = 0 → x = 0) :
    cutRatio N (Pf 1 N) = 1 / 3 := by sorry

end Supplement

end SepMeasures
