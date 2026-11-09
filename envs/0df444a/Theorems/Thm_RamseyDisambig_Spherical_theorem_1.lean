-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_theorem_1
-- name    : RamseyDisambig.Spherical.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:31:05.424194+00:00
-- url     : https://prove2.me/theorems/2dd75eff-54f1-42c7-8142-241530a931d1
-- title:
--   Theorem 1 — Spherical margin disambiguation and universality
-- statement:
--   For every real $0<\varepsilon<\pi/2$ and every natural number $k$, there is a positive threshold $d_0$ such that for every $d\ge d_0$ and every disambiguation $c$ of $M_\varepsilon^d$,
--   $$k\le\operatorname{VCdim}(c).$$
--   The row and column set is the full unit sphere $S^d\subset\mathbb R^{d+1}$. Values at angle at most $\varepsilon$ are $0$, those at angle at least $\pi-\varepsilon$ are $1$, and every other pair is filled independently. No symmetry or regularity is imposed.
--
--   In addition, for every such $\varepsilon$, the positive-dimensional family $\mathcal M_\varepsilon=(M_\varepsilon^d)_{d\ge1}$ is disambiguation-universal:
--   $$\forall a,b\in\mathbb N,\ \forall F\in\{0,1\}^{a\times b},\ \exists d\ge1,\ \forall c\text{ disambiguating }M_\varepsilon^d,\quad c\text{ contains }F.$$
--   Containment uses independent injective choices of rows and columns, including when $F$ has repeated rows. Both conclusions are retained as a single conjunction. This is the full headline obstruction to bounded-VC total extensions of the spherical margin classes.
--
--   Differences from the source:
--   - reading: sufficiently large dimensions and family {Mεd : d ≥ 1} → a positive threshold d₀ and a family indexed by ℕ+; reason: this implements the recorded positive-dimension reading without changing the eventual bound
--   - generalization: k ∈ ℕ, read positively → all k : ℕ, including k = 0; reason: the additional case follows from nonnegativity of VC-dimension
--   - encoding: unit sphere, angular distance, binary completions, containment and VC-dimension → the sphere subtype in Fin (d+1), InnerProductGeometry.angle, Option Bool, independent injective Fin maps and row-first ℕ∞ VC-dimension; reason: these represent the same points, angles, completions and finite submatrices, with both conclusions explicit
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Theorem 1, p. 4 (restated p. 13, proved p. 14; printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Sphere
import Definitions.Def_NatureSLT_GrowthFunction_vcDim

set_option autoImplicit false

namespace RamseyDisambig.Spherical

/-- Theorem 1, p. 4 (proof pp. 13–14). Both the eventual bound and universality.
The family uses all positive dimensions; the k = 0 bound is included. -/
theorem theorem_1 :
    (∀ ε : ℝ, 0 < ε → ε < Real.pi / 2 → ∀ k : ℕ,
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        ∀ c : Sphere d → Sphere d → Bool, IsSphericalDisambiguation ε d c →
          (k : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim c) ∧
    (∀ ε : ℝ, 0 < ε → ε < Real.pi / 2 → SphericalFamilyUniversal ε) := by sorry

end RamseyDisambig.Spherical
