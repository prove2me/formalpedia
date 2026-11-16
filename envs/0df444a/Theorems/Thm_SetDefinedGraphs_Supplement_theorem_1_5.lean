-- Prove2me | Theorems.Thm_SetDefinedGraphs_Supplement_theorem_1_5
-- name    : SetDefinedGraphs.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:44:19.363039+00:00
-- url     : https://prove2.me/theorems/451b6001-5218-4adb-8931-22eebb49eaef
-- title:
--   Theorem 1.5 — a nearly full set-defined class is polynomially $\chi$-bounded or contains $\vec{\mathcal S}_D$ or its symmetrization for some $D\ge2$
-- statement:
--   Let $\vec{\mathcal X}$ be a nearly full set-defined class of digraphs, that is, $\vec{\mathcal X}_f$ or $\vec{\mathcal Y}_f$ for some $d$ and some Boolean function $f:\{0,1\}^{d^2}\to\{0,1\}$. Then either $\vec{\mathcal X}$ is polynomially $\chi$-bounded, i.e. there is a polynomial $h$ with
--   $$\chi(G)\le h(\omega(G))\qquad\text{for all }G\in\vec{\mathcal X},$$
--   or, for some $D\ge2$, the class $\vec{\mathcal X}$ contains the class $\vec{\mathcal S}_D$ of $D$-dimensional shift digraphs or the class of symmetrized $D$-dimensional shift digraphs.
--
--   Since shift digraphs are triangle-free with unbounded chromatic number, the theorem identifies the only witnesses of $\chi$-unboundedness in nearly full classes; it implies the Gyárfás–Sumner conjecture for these classes (Corollary 1.6).
--
--   **Formalization Note** The statement is made for both nearly full classes $\vec{\mathcal X}_f$ (`InX f`) and $\vec{\mathcal Y}_f$ (`InY f`), for every $d$ and $f$; $D$ may depend on the class.
--
--   Differences from the source:
--
--   - encoding: "Let X⃗ be a nearly full set-defined class" → for every d and f, the conclusion for InX f (X⃗_f) and for InY f (Y⃗_f); reason: Definition 3.1 (p.15): a nearly full class is of the form X⃗_f or Y⃗_f
--   - encoding: h can be chosen to be a polynomial (h : ℕ → ℕ) → h ∈ ℕ[X], evaluated at ω(G); reason: every polynomial function ℕ → ℕ is bounded on ℕ by a polynomial with natural coefficients, and the bound χ ≤ h(ω) is monotone in h
--   - encoding: X⃗ contains the class of symmetrized D-dimensional shift digraphs → the symmetrization of every D-dimensional shift digraph is in X⃗; reason: X⃗_f and Y⃗_f are closed under isomorphism, so this is containment of the class
--   - encoding: χ(G), ω(G) of a digraph: parameters of its underlying graph → Mathlib chromaticNumber (in ℕ∞) and cliqueNum of SimpleGraph.fromRel G.Adj; reason: fromRel ignores orientation and loops, which is the paper's underlying graph (p.14); all digraphs in the classes are finite, so χ is a natural number
--   - encoding: classes of (finite) digraphs, closed under isomorphism → predicates W ↦ (Digraph W → Prop) on digraphs over arbitrary vertex types (InX, InY, InYPZ: isomorphic to a realisation over a finite V); reason: isomorphism-closed classes of finite digraphs; the paper's realisations are over finite V (p.2)
--   - encoding: Boolean function f : {0,1}^{d²} → {0,1} of the variables q_{i,j} → f : (Fin d → Fin d → Bool) → Bool, coordinate i ↦ index i − 1; reason: a function of the d² variables is a function of their value matrix; same instances
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Theorem 1.5, p.4 (PDF p.6); restated p.67 (PDF p.69); nearly full: Definition 1.1 p.2 (PDF p.4), Definition 3.1 p.15 (PDF p.17)

import Mathlib
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Supplement_ChiBoundedness

set_option autoImplicit false

namespace SetDefinedGraphs.Supplement

/-- **Theorem 1.5** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §1.1 p.4, PDF p.6; restated p.67, PDF p.69): let `X⃗` be a nearly full set-defined class of
digraphs. Then either `X⃗` is polynomially χ-bounded or, for some `D ≥ 2`, class `X⃗` contains the class `S⃗_D` of
`D`-dimensional shift digraphs or the class of symmetrized `D`-dimensional shift digraphs.

**Formalization Note** A nearly full class is `X⃗_f` (`InX f`) or `Y⃗_f` (`InY f`) for some `d` and
`f : {0,1}^{d²} → {0,1}` (Definition 3.1, p.15); the statement is made for both, for every `d` and `f`. `D` may depend on
the class. -/
theorem theorem_1_5 (d : ℕ) (f : (Fin d → Fin d → Bool) → Bool) :
    (IsPolyChiBounded (fun W G => InX (W := W) f G) ∨
      ∃ D : ℕ, 2 ≤ D ∧ (ContainsShiftDigraphs D (fun W G => InX (W := W) f G) ∨
        ContainsSymmShiftDigraphs D (fun W G => InX (W := W) f G))) ∧
    (IsPolyChiBounded (fun W G => InY (W := W) f G) ∨
      ∃ D : ℕ, 2 ≤ D ∧ (ContainsShiftDigraphs D (fun W G => InY (W := W) f G) ∨
        ContainsSymmShiftDigraphs D (fun W G => InY (W := W) f G))) := by sorry

end SetDefinedGraphs.Supplement
