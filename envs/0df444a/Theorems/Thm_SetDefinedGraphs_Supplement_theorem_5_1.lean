-- Prove2me | Theorems.Thm_SetDefinedGraphs_Supplement_theorem_5_1
-- name    : SetDefinedGraphs.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:48:03.800798+00:00
-- url     : https://prove2.me/theorems/8f9b8364-52e9-454e-a463-53534449a562
-- title:
--   Theorem 5.1 — $\vec{\mathcal Y}_{P,Z}$ has unbounded $\chi$ iff it contains some $\vec{\mathcal S}_D$, $D\ge2$, iff two $(2d-2m+k)\times d$ tropical systems have finite solutions
-- statement:
--   Let $\vec{\mathcal Y}_{P,Z}$ be the class of digraphs defined by a loopless $d$-dimensional path clause $P$ on $Z$-functional vertex sets in $\mathbb N^{\underline d}$. Let $m$ be the number of maximal paths in the clause digraph $\Delta_P$ of $P$ and $k$ the number of functional constraints in $Z$. Then there exist matrices
--   $$\widehat A,\widehat B\in\mathbb Z_{\min}^{(2d-2m+k)\times d}\quad\text{and}\quad\widetilde A,\widetilde B\in\mathbb Z_{\max}^{(2d-2m+k)\times d}$$
--   such that the following are equivalent:
--
--   1. the chromatic number of $\vec{\mathcal Y}_{P,Z}$ is unbounded;
--   2. $\vec{\mathcal Y}_{P,Z}$ contains the class $\vec{\mathcal S}_D$ of $D$-dimensional shift digraphs for some $D\ge2$;
--   3. each of the tropical inequalities $\widehat A\otimes_{\min}x\ge\widehat B\otimes_{\min}x$ and $\widetilde A\otimes_{\max}y\le\widetilde B\otimes_{\max}y$ has a finite solution.
--
--   Through the correspondence between tropical systems and mean payoff games, this turns bounded chromatic number of $\vec{\mathcal Y}_{P,Z}$ into a decidable game-theoretic condition.
--
--   **Formalization Note** The matrices are chosen from $(P,Z)$ before the conditions, and the three-way equivalence is stated as (1)⇔(2) and (2)⇔(3). $\mathbb Z_{\min}$ and $\mathbb Z_{\max}$ are `WithTop ℤ` and `WithBot ℤ`; a finite solution is a vector of $\mathbb R^d$.
--
--   Differences from the source:
--
--   - encoding: (i), (ii), (iii) are equivalent → (i ↔ ii) ∧ (ii ↔ iii); reason: the same three-way equivalence
--   - encoding: m = number of maximal paths of Δ_P (isolated vertices counted) → number of connected components of the underlying graph of Δ_P on Fin d; reason: for a loopless path clause the components are exactly the maximal paths and isolated vertices
--   - encoding: Z = ((L_1, λ_1), …, (L_k, λ_k)) with L_s ≠ [d], λ_s ∈ [d] ∖ L_s; k its number of constraints → Z : List (Finset (Fin d) × Fin d) with λ_s ∉ L_s; k = Z.length; reason: a tuple is a list; λ_s ∉ L_s implies L_s ≠ [d]
--   - encoding: ℤ_min, ℤ_max; a finite solution → WithTop ℤ, WithBot ℤ; a vector in ℝ^d (Fin d → ℝ); reason: ℤ ∪ {∞}, ℤ ∪ {−∞} with the tropical addition conventions; finite means every entry real
--   - encoding: Y⃗_{P,Z}: realisations of P over order-uniform Z-functional V ⊆ ℕ^d̲ → InYPZ P Z: isomorphic to the realisation of dnfFun {P} over a finite injective order-uniform Z-functional V; reason: the full clause P is the Boolean function of the one-clause DNF; realisations are over finite V (p.2)
--   - encoding: χ(G), ω(G) of a digraph: parameters of its underlying graph → Mathlib chromaticNumber (in ℕ∞) and cliqueNum of SimpleGraph.fromRel G.Adj; reason: fromRel ignores orientation and loops, which is the paper's underlying graph (p.14); all digraphs in the classes are finite, so χ is a natural number
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Theorem 5.1, p.35 (PDF p.37); notation §5.1.1 p.36 (PDF p.38); Y⃗_{P,Z} pp.30–31 (PDF pp.32–33)

import Mathlib
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_Supplement_ChiBoundedness
import Definitions.Def_SetDefinedGraphs_Supplement_PathClauseClass
import Definitions.Def_SetDefinedGraphs_Supplement_Tropical

set_option autoImplicit false

namespace SetDefinedGraphs.Supplement

/-- **Theorem 5.1** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §5 p.35, PDF p.37): let `Y⃗_{P,Z}` be a class of digraphs defined by a loopless
`d`-dimensional path clause `P` on `Z`-functional vertex sets in `ℕ^d̲`. Let `m` be the number of maximal paths in the
clause digraph `Δ_P` of `P` and `k` the number of functional constraints in `Z`. Then, there exist matrices
`Â, B̂ ∈ ℤ_min^{(2d−2m+k)×d}` and `Ã, B̃ ∈ ℤ_max^{(2d−2m+k)×d}` such that the following are equivalent:
(i) the chromatic number of `Y⃗_{P,Z}` is unbounded;
(ii) `Y⃗_{P,Z}` contains the class `S⃗_D` of `D`-dimensional shift digraphs for some `D ≥ 2`;
(iii) each of the tropical inequalities `Â ⊗_min x ≥ B̂ ⊗_min x` and `Ã ⊗_max y ≤ B̃ ⊗_max y` has a finite solution.

**Formalization Note** The matrices are chosen from `(P, Z)` before the three conditions; the equivalence of the three
is stated as (i) ⇔ (ii) and (ii) ⇔ (iii). `ℤ_min = WithTop ℤ`, `ℤ_max = WithBot ℤ`; a finite solution is a vector in
`ℝ^d`. `2d − 2m + k` is computed in `ℕ` and is exact, since `m ≤ d`. -/
theorem theorem_5_1 {d : ℕ} (P : FullClause (Fin d)) (hP : IsLooplessPathClause P)
    (Z : List (Finset (Fin d) × Fin d)) (hZ : IsFunctionalConstraints Z) :
    ∃ (Ahat Bhat : Matrix (Fin (2 * d - 2 * numMaxPaths P + Z.length)) (Fin d) (WithTop ℤ))
      (Atil Btil : Matrix (Fin (2 * d - 2 * numMaxPaths P + Z.length)) (Fin d) (WithBot ℤ)),
      (¬ HasBoundedChromaticNumber (InYPZ P Z) ↔
          ∃ D : ℕ, 2 ≤ D ∧ ContainsShiftDigraphs D (InYPZ P Z)) ∧
      ((∃ D : ℕ, 2 ≤ D ∧ ContainsShiftDigraphs D (InYPZ P Z)) ↔
          MinPlusHasFiniteSolution Ahat Bhat ∧ MaxPlusHasFiniteSolution Atil Btil) := by sorry

end SetDefinedGraphs.Supplement
