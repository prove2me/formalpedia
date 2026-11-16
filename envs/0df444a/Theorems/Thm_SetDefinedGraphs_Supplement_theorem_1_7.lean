-- Prove2me | Theorems.Thm_SetDefinedGraphs_Supplement_theorem_1_7
-- name    : SetDefinedGraphs.Supplement.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:45:04.716487+00:00
-- url     : https://prove2.me/theorems/037002b6-6466-42ef-907b-e7353957c02a
-- title:
--   Theorem 1.7 — $\chi$-boundedness of the nearly full classes defined by $f$ is decidable from $f$
-- statement:
--   There exists an algorithm that, given a Boolean function $f:\{0,1\}^{d^2}\to\{0,1\}$, decides whether each of the nearly full set-defined classes of digraphs defined by $f$, namely $\vec{\mathcal X}_f$ and $\vec{\mathcal Y}_f$, is $\chi$-bounded or not.
--
--   Here $d$ is part of the input: one algorithm works for all $d$. The decision procedure goes through finitely many classes $\vec{\mathcal Y}_{P,Z}$ (Theorem 4.15) and the feasibility of tropical systems (Theorem 5.1).
--
--   **Formalization Note** "There exists an algorithm" is Mathlib's `ComputablePred` on the input $(d,c)$, where $c$ lists the satisfying assignments of $f$; both predicates ($\vec{\mathcal X}_f$ and $\vec{\mathcal Y}_f$ $\chi$-bounded) are computable. For a fixed $d$ there are finitely many $f$, so a per-$d$ statement would be trivially true; this one is uniform.
--
--   Differences from the source:
--
--   - encoding: an algorithm given a Boolean function f : {0,1}^{d²} → {0,1} → Mathlib computability on the input (d, c) : ℕ × List (List (List Bool)), where c lists the satisfying d×d assignments of f = fnOfCode d c; reason: 'there exists an algorithm' is computability, independent of the machine model; every f has a code (proved: fnOfCode_surjective) and truth-table presentations are computably interconvertible; uniform in d, so not trivially true
--   - encoding: "each of the nearly full set-defined classes of digraphs defined by f" → two computable predicates: X⃗_f is χ-bounded, Y⃗_f is χ-bounded; reason: Definition 3.1: the nearly full classes defined by f are X⃗_f and Y⃗_f
--   - encoding: χ(G), ω(G) of a digraph: parameters of its underlying graph → Mathlib chromaticNumber (in ℕ∞) and cliqueNum of SimpleGraph.fromRel G.Adj; reason: fromRel ignores orientation and loops, which is the paper's underlying graph (p.14); all digraphs in the classes are finite, so χ is a natural number
--   - encoding: classes of (finite) digraphs, closed under isomorphism → predicates W ↦ (Digraph W → Prop) on digraphs over arbitrary vertex types (InX, InY, InYPZ: isomorphic to a realisation over a finite V); reason: isomorphism-closed classes of finite digraphs; the paper's realisations are over finite V (p.2)
--   - encoding: Boolean function f : {0,1}^{d²} → {0,1} of the variables q_{i,j} → f : (Fin d → Fin d → Bool) → Bool, coordinate i ↦ index i − 1; reason: a function of the d² variables is a function of their value matrix; same instances
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Theorem 1.7, p.4 (PDF p.6); restated p.68 (PDF p.70)

import Mathlib
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Supplement_ChiBoundedness
import Definitions.Def_SetDefinedGraphs_Supplement_Encoding

set_option autoImplicit false

namespace SetDefinedGraphs.Supplement

/-- **Theorem 1.7** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §1.1 p.4, PDF p.6; restated p.68, PDF p.70): there exists an algorithm that, given a
Boolean function `f : {0,1}^{d²} → {0,1}`, decides whether each of the nearly full set-defined classes of digraphs
defined by `f` is χ-bounded or not.

**Formalization Note** "There exists an algorithm" is Mathlib's computability (`ComputablePred`), uniform over all `d`:
the input is `(d, c)`, where `c` lists the satisfying assignments of `f = fnOfCode d c` (its truth table); every
Boolean function has such a code. The two nearly full classes defined by `f` are `X⃗_f` and `Y⃗_f`, and both are
decided. A per-`d` or per-`f` decidability statement would be trivially true and is not the theorem. -/
theorem theorem_1_7 :
    ComputablePred (fun c : ℕ × BoolFnCode =>
      IsChiBounded (fun W G => InX (W := W) (fnOfCode c.1 c.2) G)) ∧
    ComputablePred (fun c : ℕ × BoolFnCode =>
      IsChiBounded (fun W G => InY (W := W) (fnOfCode c.1 c.2) G)) := by sorry

end SetDefinedGraphs.Supplement
