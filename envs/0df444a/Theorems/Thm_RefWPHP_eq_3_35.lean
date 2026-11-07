-- Prove2me | Theorems.Thm_RefWPHP_eq_3_35
-- name    : RefWPHP.eq_3_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:07:54.865333+00:00
-- url     : https://prove2.me/theorems/ff37f676-5caf-46e8-b289-7d31dbb4d1bb
-- title:
--   Eq. (3.35) — local cedent for (Ref-9): constant-length PK$_2$ derivation of $\neg p_{C',b}, \neg T^{\mathrm{right}}_{C,b,c}, E_{k+1,c}$
-- statement:
--   Let $\pi$ be a layered refutation of a CNF $\varphi$, $W \in \mathbb N$, $b, c \in [W]$, and let $k$ be a layer with a next layer $k+1$. Let $C, C' \in \pi_k$, with $C$ derived with right premise $\mathrm{right}_\pi(C)$. Then $\mathrm{PHP}^L_W$ has a PK$_2$-derivation with at most $c_0$ lines of
--
--   $$
--   \neg p_{C',b},\ \neg T^{\mathrm{right}}_{C,b,c},\ E_{k+1,c},
--   $$
--
--   where $T^{\mathrm{right}}_{C,b,c} = p_{C,b}\wedge p_{\mathrm{right}_\pi(C),c}$ and $c_0$ is an absolute constant, fixed before all the data.
--
--   This local cedent is the building block for the substituted (Ref-9) clauses (3.34), which say that an enabled block only points to enabled blocks.
--
--   Differences from the source:
--   - reading: constant-size PK_2-derivation → at most c₀ lines, depth at most 2, c₀ fixed before all data; reason: E_{k+1,c} can have up to L disjuncts, so only the number of lines can be constant
--   - reading: T^right_{C,b,c} for C ∈ π_k → C is derived, with right premise r; reason: right_π(C) exists only for derived C
--   - encoding: clauses of Ref_s(φ) and PHP are written with → and ⋁ → each clause is the cedent of its literals; reason: p.15 collects a CNF into a set of cedents, and PK_0 must be Resolution; no instance changes
--   - reading: binary ∧-Intro and ∨-Intro on unbounded fan-in formulas, used in one step as "repeated ∧-introduction"; Cut on φ₁ ∧ ⋯ ∧ φ_m; cedents are sequences → PKStep: n-ary ∧/∨-introduction (0-ary ∧ gives ⊤), Atomic LEM, weakening to any list containing the premise, Cut on one formula and on a conjunction, hypotheses from Φ; dag-like lines; reason: ⊤ and ⊥ occur as formulas in (3.2)–(3.3), PK_0 must be Resolution (p.15), and the page counts repeated introductions as one step
--   - reading: logical axioms x ∨ ¬x are allowed as leaves (p.14), and the root is the final inference over a variable (p.20) → leaves are weakenings of clauses of φ, and the root is a resolution over x_{i∅}; reason: the proof of (3.23), p.23, uses that an underived clause weakens an axiom of φ; tautological clauses can be removed without changing layers, L or D, so this reading is not weaker
--   - generalization: π is a layered refutation of length L in which every root-to-leaf path has length exactly D (p.19) → LayeredRef φ L D: L bounds each layer, leaves may sit in any layer, a resolvent need only contain the union of the reduced premises; reason: the page's π is an instance (each layer has at most length(π) clauses, and a leaf at layer D is a leaf); the argument never uses the exact form
--   - encoding: layers k ∈ [D] and blocks in [s+1], with the root as block s+1 → layer k : Fin D is the paper's π_{k+1}, blocks are Fin (s+1), the root is Fin.last s, and LayeredRef requires 0 < D; reason: Lean indexing; W = ⌊s/D⌋ and the root's premises in π_1 presuppose D ≥ 1; no instance changes
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), eq. (3.35), p.25 (PDF p.27)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_phpCNF
import Definitions.Def_RefWPHP_LayeredRef
import Definitions.Def_RefWPHP_sigma

namespace RefWPHP

open PKFormula

/-- Eq. (3.35), p.25 (PDF 27), of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole
Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), the local cedent for (Ref-9):
"Fix `C, C' ∈ π_k`. We claim that `PHP^L_W` has a constant-size PK_2-derivation of
`¬p_{C',b}, ¬T^right_{C,b,c}, E_{k+1,c}`", where `T^right_{C,b,c} = p_{C,b} ∧ p_{right_π(C),c}`.

**Formalization Note.** `C` is a derived clause with right premise `r` (`T^right_{C,b,c}` needs
`right_π(C)`). "Constant-size" is a bound `c₀` on the number of lines, fixed before every object.
Layers are 0-based; `k + 1 < D` names layer `k+1`. -/
theorem eq_3_35 : ∃ c₀ : ℕ, ∀ {n m : ℕ} (φ : Fin m → Finset (Lit n)) {L D : ℕ}
    (π : LayeredRef φ L D) (W k : ℕ) (hk : k + 1 < D) (b c : Fin W) (C C' l r : Fin L)
    (i : Fin n),
    π.used ⟨k, by omega⟩ C = true → π.step ⟨k, by omega⟩ C = RStep.res i l r →
    π.used ⟨k, by omega⟩ C' = true →
    ∃ ρ : List (Cedent (Fin L × Fin W)),
      IsPKDerivationOf 2 (phpCNF L W) ρ
        [neg (C', b), dual (Tpair C r b c), E π W ⟨k + 1, hk⟩ c] ∧
      ρ.length ≤ c₀ := by sorry

end RefWPHP
