-- Prove2me | Theorems.Thm_SepMeasures_theorem_3_3
-- name    : SepMeasures.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:11:59.178038+00:00
-- url     : https://prove2.me/theorems/4e23a08a-9911-48c1-b20d-eaad8ef186ab
-- title:
--   Theorem 3.3 — for every norm on $\mathbb R^2$, $\alpha(\mathcal P^2)\ge 1/3$
-- statement:
--   Throughout, $\|\cdot\|$ is an arbitrary norm on $\mathbb R^2$. For probability measures $\mu,\nu$ on $\mathbb R^2$ with finite first moments, $L_{\mu,\nu}=\int\!\!\int\|x-y\|\,d\mu(x)\,d\nu(y)$ is the expected red–blue distance and, for an oriented affine hyperplane $H=\{u\cdot x=c\}$ ($u\neq0$) with open half-spaces $H^\pm$, $C_{\mu,\nu}(H)$ is the same integral restricted to the pairs strictly separated by $H$, $\mathrm{Sep}(H)=(H^+\times H^-)\cup(H^-\times H^+)$. The **cut ratio** of a family $\mathcal F$ is
--   $$\alpha(\mathcal F)=\inf_{(\mu,\nu)\in\mathcal F,\ L_{\mu,\nu}>0}\ \sup_{H}\ \frac{C_{\mu,\nu}(H)}{L_{\mu,\nu}}.$$
--   $\mathcal P^d$ is the family of pairs $(\mu,\nu)$ of probability measures with finite first moments whose atom sets are disjoint with union in affine general position (every at most $3$ of the points are affinely independent) and whose non-atomic parts give measure $0$ to every affine hyperplane. For every norm on $\mathbb R^2$,
--   $$\alpha(\mathcal P^2)\ \ge\ \frac13 .$$
--
--   This is the planar case of the goal theorem.
--
--   **Formalization Note** The norm is a definite seminorm $N$ on `EuclideanSpace ℝ (Fin d)`; hyperplanes are oriented pairs $(u\neq0,c)$; the cut ratio is a real infimum over the pairs with $L>0$ of a real supremum over hyperplanes, both honest because $0\le C(H)\le L$ and the family contains pairs with $L>0$.
--
--   Differences from the source:
--   - encoding: a norm ‖·‖ on ℝ² → N : Seminorm ℝ (EuclideanSpace ℝ (Fin 2)) with N x = 0 → x = 0; reason: a definite seminorm is exactly a norm; the Euclidean structure of EuclideanSpace is used only for hyperplane equations, Lebesgue measure, balls and dist(x, H), as in the paper
--   - encoding: µ_na := µ − Σ_{x∈Atom(µ)} µ({x})δ_x → µ.restrict (atoms µ)ᶜ with atoms µ = {x | µ {x} ≠ 0}; reason: for a finite measure the atom set is countable, so the two measures are equal
--   - encoding: finite first moment ∫‖x‖ dµ(x) < ∞ → ∫⁻ x, ENNReal.ofReal (N x) ∂µ < ⊤; reason: the same condition, written as a lower Lebesgue integral
--   - encoding: L_{µ,ν} and C_{µ,ν}(H) as double integrals of ‖x − y‖ → Bochner integrals of N (x − y) over µ.prod ν (restricted to Sep H for C); reason: for pairs with finite first moments the integrand is integrable, so the values are the paper's
--   - encoding: α(F) = inf over (µ,ν) ∈ F with L > 0 of sup over H ∈ ℍ^d of C(H)/L → cutRatio: ⨅ in ℝ over the pairs of F with 0 < totalDist, of ⨆ in ℝ over oriented hyperplanes Hyp d = (u ≠ 0, c); reason: the index set is non-empty for these families when d ≥ 1 and every C(H)/L lies in [0, 1], so the real ⨅ and ⨆ are the paper's inf and sup; the two orientations of a hyperplane give the same Sep(H)
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Theorem 3.3, p.20 (proof pp.20–25)

import Mathlib
import Definitions.Def_SepMeasures_CutValue
import Definitions.Def_SepMeasures_Families

open MeasureTheory

namespace SepMeasures

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Theorem 3.3, p.20 (proof pp.20–25): for every norm on
`ℝ²`, `α(𝒫²) ≥ 1/3`.

**Formalization Note.** As in Theorem 1.3, with `d = 2`; the family is `𝒫²`, as printed. -/
theorem theorem_3_3 (N : Seminorm ℝ (E 2)) (hN : ∀ x, N x = 0 → x = 0) :
    (1 / 3 : ℝ) ≤ cutRatio N (P 2 N) := by sorry

end SepMeasures
