-- Prove2me | Theorems.Thm_RefWPHP_eq_3_28
-- name    : RefWPHP.eq_3_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:06:56.376793+00:00
-- url     : https://prove2.me/theorems/fa346409-d11b-4236-a205-52c31bf9290e
-- title:
--   Eq. (3.28) — local cedent for (Ref-6): polynomial-size PK$_2$ derivation of $\neg p_{C,b}, \neg p_{C',b}, Q^{\mathrm{left}}_{k,b}$
-- statement:
--   Let $\pi$ be a layered refutation of a CNF $\varphi$, $W \in \mathbb N$, $b \in [W]$, $k$ a layer, $C, C' \in \pi_k$ with $C'$ derived. Then $\mathrm{PHP}^L_W$ has a PK$_2$-derivation of size at most $(L + W + 2)^{c_0}$ of
--
--   $$
--   \neg p_{C,b},\ \neg p_{C',b},\ P^{\mathrm{left}}_{k,b,1}, \dots, P^{\mathrm{left}}_{k,b,W},
--   $$
--
--   where $c_0$ is an absolute constant, fixed before all the data.
--
--   This local cedent is the building block for the substituted (Ref-6) clauses (3.26), and it is where the totality axioms of $\mathrm{PHP}^L_W$ enter the reduction.
--
--   Differences from the source:
--   - reading: Q^left_{k,b} = ⋁_{c∈[W]} P^left_{k,b,c} in the cedent → the list P^left_{k,b,1}, …, P^left_{k,b,W} (Qleft); reason: as one formula it would have depth 3 and could not occur in a PK_2-derivation; (Ref-6) is a clause, so the disjuncts are separate formulas
--   - reading: polynomial-size PK_2-derivation → derivSize at most (L + W + 2)^c₀ with c₀ fixed before all data; reason: L and W are the parameters of PHP^L_W, and the cedent depends on no others
--   - reading: (3.1b), (3.1c): P^left_{k,b,c}, P^right_{k,b,c} range over C ∈ π_k → they range over the derived C ∈ π_k; reason: left_π(C) and right_π(C) exist only for derived C
--   - encoding: size is the length of a binary string (p.15) → symbol count plus one per line (derivSize); reason: the two differ by at most a logarithmic factor in the number of variables, which the polynomial absorbs
--   - encoding: clauses of Ref_s(φ) and PHP are written with → and ⋁ → each clause is the cedent of its literals; reason: p.15 collects a CNF into a set of cedents, and PK_0 must be Resolution; no instance changes
--   - reading: binary ∧-Intro and ∨-Intro on unbounded fan-in formulas, used in one step as "repeated ∧-introduction"; Cut on φ₁ ∧ ⋯ ∧ φ_m; cedents are sequences → PKStep: n-ary ∧/∨-introduction (0-ary ∧ gives ⊤), Atomic LEM, weakening to any list containing the premise, Cut on one formula and on a conjunction, hypotheses from Φ; dag-like lines; reason: ⊤ and ⊥ occur as formulas in (3.2)–(3.3), PK_0 must be Resolution (p.15), and the page counts repeated introductions as one step
--   - reading: logical axioms x ∨ ¬x are allowed as leaves (p.14), and the root is the final inference over a variable (p.20) → leaves are weakenings of clauses of φ, and the root is a resolution over x_{i∅}; reason: the proof of (3.23), p.23, uses that an underived clause weakens an axiom of φ; tautological clauses can be removed without changing layers, L or D, so this reading is not weaker
--   - generalization: π is a layered refutation of length L in which every root-to-leaf path has length exactly D (p.19) → LayeredRef φ L D: L bounds each layer, leaves may sit in any layer, a resolvent need only contain the union of the reduced premises; reason: the page's π is an instance (each layer has at most length(π) clauses, and a leaf at layer D is a leaf); the argument never uses the exact form
--   - encoding: layers k ∈ [D] and blocks in [s+1], with the root as block s+1 → layer k : Fin D is the paper's π_{k+1}, blocks are Fin (s+1), the root is Fin.last s, and LayeredRef requires 0 < D; reason: Lean indexing; W = ⌊s/D⌋ and the root's premises in π_1 presuppose D ≥ 1; no instance changes
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), eq. (3.28), p.24 (PDF p.26)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_phpCNF
import Definitions.Def_RefWPHP_LayeredRef
import Definitions.Def_RefWPHP_sigma

namespace RefWPHP

open PKFormula

/-- Eq. (3.28), p.24 (PDF 26), of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole
Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), the local cedent for (Ref-6):
"Fix `C, C' ∈ π_k`, where `C'` is derived. We claim that `PHP^L_W` has a polynomial-size
PK_2-derivation of `¬p_{C,b}, ¬p_{C',b}, Q^left_{k,b}`", with
`Q^left_{k,b} = ⋁_{c ∈ [W]} P^left_{k,b,c}`.

**Formalization Note.** `Q^left_{k,b}` is the list `P^left_{k,b,1}, …, P^left_{k,b,W}` (`Qleft`), the
disjunction of the substituted cedent (3.26); as one formula it would have depth 3. "Polynomial-size"
is size at most `(L + W + 2)^c₀` with `c₀` fixed before every object; `L` and `W` are the parameters
of `PHP^L_W`. `C'` is derived: it resolves over some `x_i` from slots `l`, `r`. Layer `k : Fin D` is
the paper's `π_{k+1}`. -/
theorem eq_3_28 : ∃ c₀ : ℕ, ∀ {n m : ℕ} (φ : Fin m → Finset (Lit n)) {L D : ℕ}
    (π : LayeredRef φ L D) (W : ℕ) (k : Fin D) (b : Fin W) (C C' l r : Fin L) (i : Fin n),
    π.used k C = true → π.used k C' = true → π.step k C' = RStep.res i l r →
    ∃ ρ : List (Cedent (Fin L × Fin W)),
      IsPKDerivationOf 2 (phpCNF L W) ρ (neg (C, b) :: neg (C', b) :: Qleft π W k b) ∧
      derivSize ρ ≤ (L + W + 2) ^ c₀ := by sorry

end RefWPHP
