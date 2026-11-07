-- Prove2me | Theorems.Thm_RefWPHP_eq_3_6
-- name    : RefWPHP.eq_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:05:55.465199+00:00
-- url     : https://prove2.me/theorems/a748b568-8353-492e-88c6-c8d65a1b5763
-- title:
--   Eq. (3.6) — local cedent for (Ref-1): constant-length PK$_2$ derivation of $\neg T^{\mathrm{left}}_{C,b,c}, \neg p_{C',b}, \neg p_{D,c}, L_{k,b,\ell}$
-- statement:
--   Let $\pi$ be a layered refutation of a CNF $\varphi$, $W \in \mathbb N$, $b, c \in [W]$, and let $k$ be a layer with a next layer $k+1$. Let $C, C' \in \pi_k$ and $D \in \pi_{k+1}$, where $C$ is derived with left premise $\mathrm{left}_\pi(C)$, $C'$ resolves over $x_i$, and $\ell \in D$ with $\ell \ne x_i$. Then $\mathrm{PHP}^L_W$ has a PK$_2$-derivation with at most $c_0$ lines of
--
--   $$
--   \neg T^{\mathrm{left}}_{C,b,c},\ \neg p_{C',b},\ \neg p_{D,c},\ L_{k,b,\ell},
--   $$
--
--   where $T^{\mathrm{left}}_{C,b,c} = p_{C,b}\wedge p_{\mathrm{left}_\pi(C),c}$ and $c_0$ is an absolute constant, fixed before all the data.
--
--   This local cedent is the building block for the substituted (Ref-1) clauses (3.5).
--
--   **Formalization Note** "Constant-size" cannot bound the symbol count, since $L_{k,b,\ell}$ can have up to $L$ disjuncts; it is a bound on the number of lines.
--
--   Differences from the source:
--   - generalization: ℓ is a literal over a variable other than x_i, as (3.4) says → ℓ is any literal other than x_i, so ℓ = ¬x_i is included; reason: (Ref-1) ranges over Lit_n \ {x_i}, which (3.4) leaves out; the same argument covers it and specializes to the page's ℓ
--   - reading: constant-size PK_2-derivation → at most c₀ lines, depth at most 2, c₀ fixed before all data; reason: the cedent itself can have size of order L, so only the number of lines can be constant
--   - reading: T^left_{C,b,c} for C ∈ π_k → C is derived, with left premise lC; reason: left_π(C) exists only for derived C
--   - reading: binary ∧-Intro and ∨-Intro on unbounded fan-in formulas, used in one step as "repeated ∧-introduction"; Cut on φ₁ ∧ ⋯ ∧ φ_m; cedents are sequences → PKStep: n-ary ∧/∨-introduction (0-ary ∧ gives ⊤), Atomic LEM, weakening to any list containing the premise, Cut on one formula and on a conjunction, hypotheses from Φ; dag-like lines; reason: ⊤ and ⊥ occur as formulas in (3.2)–(3.3), PK_0 must be Resolution (p.15), and the page counts repeated introductions as one step
--   - reading: logical axioms x ∨ ¬x are allowed as leaves (p.14), and the root is the final inference over a variable (p.20) → leaves are weakenings of clauses of φ, and the root is a resolution over x_{i∅}; reason: the proof of (3.23), p.23, uses that an underived clause weakens an axiom of φ; tautological clauses can be removed without changing layers, L or D, so this reading is not weaker
--   - generalization: π is a layered refutation of length L in which every root-to-leaf path has length exactly D (p.19) → LayeredRef φ L D: L bounds each layer, leaves may sit in any layer, a resolvent need only contain the union of the reduced premises; reason: the page's π is an instance (each layer has at most length(π) clauses, and a leaf at layer D is a leaf); the argument never uses the exact form
--   - encoding: layers k ∈ [D] and blocks in [s+1], with the root as block s+1 → layer k : Fin D is the paper's π_{k+1}, blocks are Fin (s+1), the root is Fin.last s, and LayeredRef requires 0 < D; reason: Lean indexing; W = ⌊s/D⌋ and the root's premises in π_1 presuppose D ≥ 1; no instance changes
--   - encoding: clauses of PHP are written with ⋁ → each clause is the cedent of its literals; reason: p.15 collects a CNF into a set of cedents, and PK_0 must be Resolution; no instance changes
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), eq. (3.6), p.21 (PDF p.23)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_phpCNF
import Definitions.Def_RefWPHP_LayeredRef
import Definitions.Def_RefWPHP_sigma

namespace RefWPHP

open PKFormula

/-- Eq. (3.6), p.21 (PDF 23), of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole
Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), the local cedent for (Ref-1):
"Fix `C, C' ∈ π_k`, `D ∈ π_{k+1}`, where `C'` resolves over `x_i` and `ℓ ∈ D`. We claim that
`PHP^L_W` has a constant-size PK_2-derivation of `¬T^left_{C,b,c}, ¬p_{C',b}, ¬p_{D,c}, L_{k,b,ℓ}`",
where `T^left_{C,b,c} = p_{C,b} ∧ p_{left_π(C),c}` and, as in (3.4), `ℓ` is not the pivot literal.

The page takes `ℓ` "a literal over a variable other than `x_i`"; here `ℓ` is any literal other than
`x_i`, the literals (Ref-1) ranges over (`Lit_n \ {x_i}`), so `ℓ = ¬x_i` is included.

**Formalization Note.** "Constant-size" is a bound `c₀` on the number of lines, fixed before every
object (the cedent itself has size up to `L`). `C` is a derived clause with left premise `lC`
(`T^left_{C,b,c}` needs `left_π(C)`). Layers are 0-based; `k + 1 < D` names layer `k+1`. -/
theorem eq_3_6 : ∃ c₀ : ℕ, ∀ {n m : ℕ} (φ : Fin m → Finset (Lit n)) {L D : ℕ}
    (π : LayeredRef φ L D) (W k : ℕ) (hk : k + 1 < D) (b c : Fin W)
    (C C' Dc lC rC l' r' : Fin L) (j i : Fin n) (ℓ : Lit n),
    π.used ⟨k, by omega⟩ C = true → π.step ⟨k, by omega⟩ C = RStep.res j lC rC →
    π.used ⟨k, by omega⟩ C' = true → π.step ⟨k, by omega⟩ C' = RStep.res i l' r' →
    π.used ⟨k + 1, hk⟩ Dc = true → ℓ ∈ π.clause ⟨k + 1, hk⟩ Dc → ℓ ≠ (i, true) →
    ∃ ρ : List (Cedent (Fin L × Fin W)),
      IsPKDerivationOf 2 (phpCNF L W) ρ
        [dual (Tpair C lC b c), neg (C', b), neg (Dc, c), Lsub π W ⟨k, by omega⟩ b ℓ] ∧
      ρ.length ≤ c₀ := by sorry

end RefWPHP
