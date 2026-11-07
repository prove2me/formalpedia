-- Prove2me | Theorems.Thm_RefWPHP_eq_3_23
-- name    : RefWPHP.eq_3_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:06:48.305213+00:00
-- url     : https://prove2.me/theorems/cd153c04-9ebf-4bef-952b-72e99c89adbe
-- title:
--   Eq. (3.23) — local cedent for (Ref-5): constant-length PK$_2$ derivation of $\neg p_{C,b}, R_{k,b}, W_{k,b}$
-- statement:
--   Let $\pi$ be a layered refutation of a CNF $\varphi$, $W \in \mathbb N$, $b \in [W]$, $k$ a layer and $C \in \pi_k$. Then there is a PK$_2$-derivation from no axioms, with at most $c_0$ lines, of
--
--   $$
--   \neg p_{C,b},\ R_{k,b},\ W_{k,b,1}, \dots, W_{k,b,m},
--   $$
--
--   where $R_{k,b} = \bigvee_{i\in[n]} R_{k,b,i}$ and $c_0$ is an absolute constant, fixed before all the data.
--
--   This local cedent is the building block for the substituted (Ref-5) clauses (3.22); it records that every clause of a layer is either derived or a weakening of an axiom.
--
--   Differences from the source:
--   - reading: W_{k,b} = ⋁_{A∈[m]} W_{k,b,A} in the cedent → the list W_{k,b,1}, …, W_{k,b,m} (Wall); reason: (Ref-5) is a clause, so the substituted cedent has its disjuncts as separate formulas; one ∨-introduction gives the page's formula
--   - reading: constant-size PK_2-derivation, with no axioms of PHP used (p.23) → at most c₀ lines, depth at most 2, from the empty set of cedents; reason: the cedent's size grows with L, n and m, so only the number of lines can be constant
--   - reading: binary ∧-Intro and ∨-Intro on unbounded fan-in formulas, used in one step as "repeated ∧-introduction"; Cut on φ₁ ∧ ⋯ ∧ φ_m; cedents are sequences → PKStep: n-ary ∧/∨-introduction (0-ary ∧ gives ⊤), Atomic LEM, weakening to any list containing the premise, Cut on one formula and on a conjunction, hypotheses from Φ; dag-like lines; reason: ⊤ and ⊥ occur as formulas in (3.2)–(3.3), PK_0 must be Resolution (p.15), and the page counts repeated introductions as one step
--   - reading: logical axioms x ∨ ¬x are allowed as leaves (p.14), and the root is the final inference over a variable (p.20) → leaves are weakenings of clauses of φ, and the root is a resolution over x_{i∅}; reason: the proof of (3.23), p.23, uses that an underived clause weakens an axiom of φ; tautological clauses can be removed without changing layers, L or D, so this reading is not weaker
--   - generalization: π is a layered refutation of length L in which every root-to-leaf path has length exactly D (p.19) → LayeredRef φ L D: L bounds each layer, leaves may sit in any layer, a resolvent need only contain the union of the reduced premises; reason: the page's π is an instance (each layer has at most length(π) clauses, and a leaf at layer D is a leaf); the argument never uses the exact form
--   - encoding: layers k ∈ [D] and blocks in [s+1], with the root as block s+1 → layer k : Fin D is the paper's π_{k+1}, blocks are Fin (s+1), the root is Fin.last s, and LayeredRef requires 0 < D; reason: Lean indexing; W = ⌊s/D⌋ and the root's premises in π_1 presuppose D ≥ 1; no instance changes
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), eq. (3.23), p.23 (PDF p.25)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_LayeredRef
import Definitions.Def_RefWPHP_sigma

namespace RefWPHP

open PKFormula

/-- Eq. (3.23), p.23 (PDF 25), of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole
Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), the local cedent for (Ref-5):
"Fix `C ∈ π_k`. We claim that there is a constant-size PK_2-derivation of
`¬p_{C,b}, R_{k,b}, W_{k,b}`", with `R_{k,b} = ⋁ᵢ R_{k,b,i}` and `W_{k,b} = ⋁_A W_{k,b,A}`.

**Formalization Note.** `R_{k,b}` is the formula `σ_{π,s}(derived^{B_{k,b}})` (`Rall`); `W_{k,b}` is
the list `W_{k,b,1}, …, W_{k,b,m}` (`Wall`), the disjunction of the substituted cedent (3.22). The
page claims the derivation without axioms ("No axioms of PHP^L_W are used"), so it is a derivation
from the empty set of cedents. "Constant-size" is a bound `c₀` on the number of lines, fixed before
every object (the cedent itself can have size of order `L·(n + m)`). Layer `k : Fin D` is the
paper's `π_{k+1}`; `W` is any number of holes. -/
theorem eq_3_23 : ∃ c₀ : ℕ, ∀ {n m : ℕ} (φ : Fin m → Finset (Lit n)) {L D : ℕ}
    (π : LayeredRef φ L D) (W : ℕ) (k : Fin D) (b : Fin W) (C : Fin L),
    π.used k C = true →
    ∃ ρ : List (Cedent (Fin L × Fin W)),
      IsPKDerivationOf 2 (∅ : Set (Cedent (Fin L × Fin W))) ρ
        (neg (C, b) :: Rall π W k b :: Wall π W k b) ∧
      ρ.length ≤ c₀ := by sorry

end RefWPHP
