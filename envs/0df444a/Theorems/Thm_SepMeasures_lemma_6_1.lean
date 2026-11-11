-- Prove2me | Theorems.Thm_SepMeasures_lemma_6_1
-- name    : SepMeasures.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:11:39.329556+00:00
-- url     : https://prove2.me/theorems/255512b5-d539-4866-a035-0433ac8c5ada
-- title:
--   Lemma 6.1 — reduction to bounded support: $\alpha(\mathcal P^d)\ge\alpha(\mathcal P^d_b)$
-- statement:
--   Throughout, $\|\cdot\|$ is an arbitrary norm on $\mathbb R^d$. For probability measures $\mu,\nu$ on $\mathbb R^d$ with finite first moments, $L_{\mu,\nu}=\int\!\!\int\|x-y\|\,d\mu(x)\,d\nu(y)$ is the expected red–blue distance and, for an oriented affine hyperplane $H=\{u\cdot x=c\}$ ($u\neq0$) with open half-spaces $H^\pm$, $C_{\mu,\nu}(H)$ is the same integral restricted to the pairs strictly separated by $H$, $\mathrm{Sep}(H)=(H^+\times H^-)\cup(H^-\times H^+)$. The **cut ratio** of a family $\mathcal F$ is
--   $$\alpha(\mathcal F)=\inf_{(\mu,\nu)\in\mathcal F,\ L_{\mu,\nu}>0}\ \sup_{H}\ \frac{C_{\mu,\nu}(H)}{L_{\mu,\nu}}.$$
--   $\mathcal P^d$ is the family of pairs $(\mu,\nu)$ of probability measures with finite first moments whose atom sets are disjoint with union in affine general position (every at most $d+1$ of the points are affinely independent) and whose non-atomic parts give measure $0$ to every affine hyperplane. $\mathcal P^d_b$ consists of the pairs of $\mathcal P^d$ in which both measures have bounded support. For every $d\ge1$ and every norm on $\mathbb R^d$,
--   $$\alpha(\mathcal P^d)\ \ge\ \alpha(\mathcal P^d_b).$$
--
--   Together with the trivial inclusion $\mathcal P^d_b\subseteq\mathcal P^d$ this shows the two cut ratios agree, so lower bounds may be proved for boundedly supported measures.
--
--   **Formalization Note** The norm is a definite seminorm $N$ on `EuclideanSpace ℝ (Fin d)`; hyperplanes are oriented pairs $(u\neq0,c)$; the cut ratio is a real infimum over the pairs with $L>0$ of a real supremum over hyperplanes, both honest because $0\le C(H)\le L$ and the family contains pairs with $L>0$.
--
--   Differences from the source:
--   - encoding: a norm ‖·‖ on ℝ^d → N : Seminorm ℝ (EuclideanSpace ℝ (Fin d)) with N x = 0 → x = 0; reason: a definite seminorm is exactly a norm; the Euclidean structure of EuclideanSpace is used only for hyperplane equations, Lebesgue measure, balls and dist(x, H), as in the paper
--   - encoding: µ_na := µ − Σ_{x∈Atom(µ)} µ({x})δ_x → µ.restrict (atoms µ)ᶜ with atoms µ = {x | µ {x} ≠ 0}; reason: for a finite measure the atom set is countable, so the two measures are equal
--   - encoding: finite first moment ∫‖x‖ dµ(x) < ∞ → ∫⁻ x, ENNReal.ofReal (N x) ∂µ < ⊤; reason: the same condition, written as a lower Lebesgue integral
--   - encoding: L_{µ,ν} and C_{µ,ν}(H) as double integrals of ‖x − y‖ → Bochner integrals of N (x − y) over µ.prod ν (restricted to Sep H for C); reason: for pairs with finite first moments the integrand is integrable, so the values are the paper's
--   - encoding: α(F) = inf over (µ,ν) ∈ F with L > 0 of sup over H ∈ ℍ^d of C(H)/L → cutRatio: ⨅ in ℝ over the pairs of F with 0 < totalDist, of ⨆ in ℝ over oriented hyperplanes Hyp d = (u ≠ 0, c); reason: the index set is non-empty for these families when d ≥ 1 and every C(H)/L lies in [0, 1], so the real ⨅ and ⨆ are the paper's inf and sup; the two orientations of a hyperplane give the same Sep(H)
--   - encoding: both measures have bounded support (𝒫^d_b) → both measures vanish outside a common closed Euclidean ball closedBall 0 R; reason: a set is bounded iff it lies in such a ball
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Lemma 6.1, p.45 (proof pp.45–46); standing assumptions of §2 and §6, pp.10, 44

import Mathlib
import Definitions.Def_SepMeasures_CutValue
import Definitions.Def_SepMeasures_Families

open MeasureTheory

namespace SepMeasures

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Lemma 6.1, p.45 (proof pp.45–46): `α(𝒫^d) ≥ α(𝒫^d_b)`,
for every `d ≥ 1` and every norm on `ℝ^d` (the standing assumptions of §2 and §6, pp.10, 44).

**Formalization Note.** Both families contain pairs with `L > 0` for `d ≥ 1`, so both cut
ratios are honest infima. -/
theorem lemma_6_1 (d : ℕ) (hd : 1 ≤ d) (N : Seminorm ℝ (E d)) (hN : ∀ x, N x = 0 → x = 0) :
    cutRatio N (Pb d N) ≤ cutRatio N (P d N) := by sorry

end SepMeasures
