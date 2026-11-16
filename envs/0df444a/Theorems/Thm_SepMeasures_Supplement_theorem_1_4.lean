-- Prove2me | Theorems.Thm_SepMeasures_Supplement_theorem_1_4
-- name    : SepMeasures.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:17:06.008999+00:00
-- url     : https://prove2.me/theorems/344a64fe-85ce-41ad-941f-54f1fecf9151
-- title:
--   Theorem 1.4 — for every $d\ge2$ and every norm on $\mathbb R^d$, $\alpha(\mathcal P^d)\le 1/2$
-- statement:
--   Let $d\ge2$ and let $\|\cdot\|$ be any norm on $\mathbb R^d$. Let $\mathcal P^d$ be the family of pairs $(\mu,\nu)$ of probability measures on $\mathbb R^d$ with finite first moments, disjoint atom sets whose union is in affine general position, and non-atomic parts that give zero mass to every affine hyperplane. With $L_{\mu,\nu}=\mathbb E\|X-Y\|$ and $C_{\mu,\nu}(H)$ the part of it carried by pairs strictly separated by the hyperplane $H$,
--   $$\alpha(\mathcal P^d)=\inf_{\substack{(\mu,\nu)\in\mathcal P^d\\ L_{\mu,\nu}>0}}\ \sup_{H}\frac{C_{\mu,\nu}(H)}{L_{\mu,\nu}}\ \le\ \frac12 .$$
--
--   Together with the lower bound $\alpha(\mathcal P^d)\ge1/3$ (Theorem 1.3), this brackets the optimal guarantee in every dimension $d\ge2$, for every norm.
--
--   **Formalization Note** The carrier is `EuclideanSpace ℝ (Fin d)` with an arbitrary seminorm $N$ satisfying $N(x)=0\Rightarrow x=0$; $\mathcal P^d$ and $\alpha$ are the published `SepMeasures.P` and `SepMeasures.cutRatio`. $\mathcal P^d$ contains pairs with $L>0$, so the bound is not met by Lean's value $0$ for an infimum over the empty set.
--
--   Differences from the source:
--   - encoding: a norm on ℝ^d → a seminorm N on EuclideanSpace ℝ (Fin d) with N x = 0 → x = 0; reason: Lean convention for an arbitrary (non-Euclidean) norm on the Euclidean carrier; same instances
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Theorem 1.4, p.6 (restated and proved pp.35–36)

import Mathlib
import Definitions.Def_SepMeasures_CutValue
import Definitions.Def_SepMeasures_Families

open MeasureTheory

namespace SepMeasures

namespace Supplement

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Theorem 1.4, p.6 (restated and proved pp.35–36): for every
`d ≥ 2` and every norm on `ℝ^d`, `α(𝒫^d) ≤ 1/2`.

**Formalization Note.** The norm is a `Seminorm` `N` on `EuclideanSpace ℝ (Fin d)` with
`N x = 0 → x = 0`; the family is the published `𝒫^d` and `cutRatio` the published Definition 2.1.
`𝒫^d` contains a pair with `L > 0` for `d ≥ 1`, so the infimum is over a non-empty set and the
upper bound is not satisfied by Lean's empty-index value `0`. -/
theorem theorem_1_4 (d : ℕ) (hd : 2 ≤ d) (N : Seminorm ℝ (E d)) (hN : ∀ x, N x = 0 → x = 0) :
    cutRatio N (P d N) ≤ 1 / 2 := by sorry

end Supplement

end SepMeasures
