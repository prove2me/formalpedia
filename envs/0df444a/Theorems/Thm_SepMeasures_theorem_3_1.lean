-- Prove2me | Theorems.Thm_SepMeasures_theorem_3_1
-- name    : SepMeasures.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:11:46.191719+00:00
-- url     : https://prove2.me/theorems/571e5141-61cb-4037-9063-3cce16cc2277
-- title:
--   Theorem 3.1 — for every norm on $\mathbb R$, $\alpha(\mathcal P^1_f)\ge 1/3$
-- statement:
--   Throughout, $\|\cdot\|$ is an arbitrary norm on $\mathbb R$. For probability measures $\mu,\nu$ on $\mathbb R$ with finite first moments, $L_{\mu,\nu}=\int\!\!\int\|x-y\|\,d\mu(x)\,d\nu(y)$ is the expected red–blue distance and, for an oriented affine hyperplane $H=\{u\cdot x=c\}$ ($u\neq0$) with open half-spaces $H^\pm$, $C_{\mu,\nu}(H)$ is the same integral restricted to the pairs strictly separated by $H$, $\mathrm{Sep}(H)=(H^+\times H^-)\cup(H^-\times H^+)$. The **cut ratio** of a family $\mathcal F$ is
--   $$\alpha(\mathcal F)=\inf_{(\mu,\nu)\in\mathcal F,\ L_{\mu,\nu}>0}\ \sup_{H}\ \frac{C_{\mu,\nu}(H)}{L_{\mu,\nu}}.$$
--   On the line a hyperplane is a threshold $\tau$, and $\mathcal P^1_f$ is the family of **all** pairs of probability measures on $\mathbb R$ with finite first moments (no condition on atoms). For every norm on $\mathbb R$,
--   $$\alpha(\mathcal P^1_f)\ \ge\ \frac13 .$$
--
--   This is the one-dimensional case of the goal theorem (and of the lower half of Theorem 1.1); since $\mathcal P^1\subseteq\mathcal P^1_f$, it gives the goal for $d=1$.
--
--   **Formalization Note** $\mathbb R$ is `EuclideanSpace ℝ (Fin 1)` and the norm a definite seminorm $N$ on it; the cut ratio is a real infimum over pairs with $L>0$ of a real supremum over oriented thresholds, with strict separation.
--
--   Differences from the source:
--   - encoding: ℝ → EuclideanSpace ℝ (Fin 1); reason: an isometric copy of ℝ; its hyperplanes are the thresholds {x | u x = c}, u ≠ 0
--   - encoding: a norm on ℝ → N : Seminorm ℝ (EuclideanSpace ℝ (Fin 1)) with N x = 0 → x = 0; reason: a definite seminorm is exactly a norm; the Euclidean structure of EuclideanSpace is used only for hyperplane equations, Lebesgue measure, balls and dist(x, H), as in the paper
--   - encoding: finite first moment ∫‖x‖ dµ(x) < ∞ → ∫⁻ x, ENNReal.ofReal (N x) ∂µ < ⊤; reason: the same condition, written as a lower Lebesgue integral
--   - encoding: L_{µ,ν} and C_{µ,ν}(H) as double integrals of ‖x − y‖ → Bochner integrals of N (x − y) over µ.prod ν (restricted to Sep H for C); reason: for pairs with finite first moments the integrand is integrable, so the values are the paper's
--   - encoding: α(F) = inf over (µ,ν) ∈ F with L > 0 of sup over H ∈ ℍ^d of C(H)/L → cutRatio: ⨅ in ℝ over the pairs of F with 0 < totalDist, of ⨆ in ℝ over oriented hyperplanes Hyp d = (u ≠ 0, c); reason: the index set is non-empty for these families when d ≥ 1 and every C(H)/L lies in [0, 1], so the real ⨅ and ⨆ are the paper's inf and sup; the two orientations of a hyperplane give the same Sep(H)
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Theorem 3.1, p.15 (proof pp.15–17)

import Mathlib
import Definitions.Def_SepMeasures_CutValue
import Definitions.Def_SepMeasures_Families

open MeasureTheory

namespace SepMeasures

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Theorem 3.1, p.15 (proof pp.15–17): for every
norm on `ℝ`, `α(𝒫^1_f) ≥ 1/3`.

**Formalization Note.** `ℝ` is `EuclideanSpace ℝ (Fin 1)`; a norm on it is a `Seminorm` `N`
with `N x = 0 → x = 0`. The family is `𝒫^1_f` (probability measures with finite first
moments, no geometric condition); hyperplanes of `ℝ` are thresholds, and separation is strict. -/
theorem theorem_3_1 (N : Seminorm ℝ (E 1)) (hN : ∀ x, N x = 0 → x = 0) :
    (1 / 3 : ℝ) ≤ cutRatio N (Pf 1 N) := by sorry

end SepMeasures
