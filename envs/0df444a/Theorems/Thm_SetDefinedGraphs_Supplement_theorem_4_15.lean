-- Prove2me | Theorems.Thm_SetDefinedGraphs_Supplement_theorem_4_15
-- name    : SetDefinedGraphs.Supplement.theorem_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:47:17.616148+00:00
-- url     : https://prove2.me/theorems/38e990ab-c789-42ea-a971-0206f308d47f
-- title:
--   Theorem 4.15 — $\vec{\mathcal X}_f$ is $\chi$-bounded iff each of $r\le d^{2d}\cdot2^{d^2}\cdot d^{2^{d^2}}$ computable classes $\vec{\mathcal Y}_{P_i,Z_i}$ has bounded chromatic number
-- statement:
--   Let $f:\{0,1\}^{d^2}\to\{0,1\}$. There exist
--   $$r\le d^{2d}\cdot2^{d^2}\cdot d^{2^{d^2}}$$
--   classes $\vec{\mathcal Y}_{P_1,Z_1},\dots,\vec{\mathcal Y}_{P_r,Z_r}$, each given by a loopless path clause $P_i$ and a tuple $Z_i$ of functional constraints, such that $\vec{\mathcal X}_f$ is $\chi$-bounded if and only if each of the classes $\vec{\mathcal Y}_{P_i,Z_i}$, $i\in[r]$, has bounded chromatic number. Furthermore, the pairs $(P_i,Z_i)$, $i\in[r]$, can be computed from $f$.
--
--   This reduces the decision problem of Theorem 1.7 for full classes to finitely many path-clause classes, which Theorem 5.1 handles.
--
--   **Formalization Note** One computable map (Mathlib's `Computable`, uniform in $d$) sends the code of $f$ to the list of codes of the pairs $(P_i,Z_i)$; its length is $r$. Each $P_i$ is a clause over $d_i'^2$ variables with $d_i'\le d$, as the proof (p.34) produces via Lemma 4.18.
--
--   Differences from the source:
--
--   - encoding: there exist r classes Y⃗_{P_i,Z_i} …; furthermore the pairs (P_i, Z_i) can be computed from f → ∃ computable g : ℕ × BoolFnCode → List PZCode such that for every (d, c), with f = fnOfCode d c, the list g(d, c) has length r ≤ the bound, all its codes are valid, and the iff holds; reason: the computed pairs are the theorem's pairs; computability on finite codes, independent of the machine model, uniform in d
--   - reading: classes Y⃗_{P_i,Z_i} with P_i a loopless path clause "over d² variables" (notation of p.30) → P_i a loopless path clause over d_i′² variables, Z_i functional constraints over [d_i′], with d_i′ ≤ d; reason: the printed notation leaves the dimension of the produced classes implicit; the proof (p.34) produces F′_i over d′² variables for some d′ ≤ d via Lemma 4.18
--   - encoding: an algorithm given a Boolean function f : {0,1}^{d²} → {0,1} → Mathlib computability on the input (d, c) : ℕ × List (List (List Bool)), where c lists the satisfying d×d assignments of f = fnOfCode d c; reason: 'there exists an algorithm' is computability, independent of the machine model; every f has a code (proved: fnOfCode_surjective) and truth-table presentations are computably interconvertible; uniform in d, so not trivially true
--   - encoding: χ(G), ω(G) of a digraph: parameters of its underlying graph → Mathlib chromaticNumber (in ℕ∞) and cliqueNum of SimpleGraph.fromRel G.Adj; reason: fromRel ignores orientation and loops, which is the paper's underlying graph (p.14); all digraphs in the classes are finite, so χ is a natural number
--   - encoding: classes of (finite) digraphs, closed under isomorphism → predicates W ↦ (Digraph W → Prop) on digraphs over arbitrary vertex types (InX, InY, InYPZ: isomorphic to a realisation over a finite V); reason: isomorphism-closed classes of finite digraphs; the paper's realisations are over finite V (p.2)
--   - encoding: Boolean function f : {0,1}^{d²} → {0,1} of the variables q_{i,j} → f : (Fin d → Fin d → Bool) → Bool, coordinate i ↦ index i − 1; reason: a function of the d² variables is a function of their value matrix; same instances
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Theorem 4.15, p.31 (PDF p.33); restated p.34 (PDF p.36); Y⃗_{P,Z} defined pp.30–31 (PDF pp.32–33)

import Mathlib
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Supplement_ChiBoundedness
import Definitions.Def_SetDefinedGraphs_Supplement_PathClauseClass
import Definitions.Def_SetDefinedGraphs_Supplement_Encoding

set_option autoImplicit false

namespace SetDefinedGraphs.Supplement

/-- **Theorem 4.15** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §4.5 p.31, PDF p.33; restated p.34, PDF p.36): let `f : {0,1}^{d²} → {0,1}`. There exist
`r ≤ d^{2d} · 2^{d²} · d^{2^{d²}}` classes `Y⃗_{P₁,Z₁}, …, Y⃗_{P_r,Z_r}` such that `X⃗_f` is χ-bounded if and only if each
of the classes `Y⃗_{P_i,Z_i}`, `i ∈ [r]`, has bounded chromatic number. Furthermore, the pairs `(P_i, Z_i)`, `i ∈ [r]`,
can be computed from `f`.

**Formalization Note** One computable map `g` (Mathlib's `Computable`, uniform over all `d`) sends the input `(d, c)`
(`c` lists the satisfying assignments of `f = fnOfCode d c`) to the list of codes of the pairs `(P_i, Z_i)`; its length
is `r`. Each code is valid: `P_i` is a loopless path clause over `d_i′²` variables and `Z_i` a tuple of functional
constraints over `[d_i′]`, with `d_i′ ≤ d` (the proof, p.34, produces classes of dimension `d′ ≤ d` via Lemma 4.18). -/
theorem theorem_4_15 :
    ∃ g : ℕ × BoolFnCode → List PZCode, Computable g ∧
      ∀ (d : ℕ) (c : BoolFnCode),
        (g (d, c)).length ≤ d ^ (2 * d) * 2 ^ (d ^ 2) * d ^ (2 ^ (d ^ 2)) ∧
        (∀ x ∈ g (d, c), IsValidPZCode x ∧ x.1 ≤ d) ∧
        (IsChiBounded (fun W G => InX (W := W) (fnOfCode d c) G) ↔
          ∀ x ∈ g (d, c), HasBoundedChromaticNumber (InYPZ (pzClause x) (pzConstraints x))) := by sorry

end SetDefinedGraphs.Supplement
