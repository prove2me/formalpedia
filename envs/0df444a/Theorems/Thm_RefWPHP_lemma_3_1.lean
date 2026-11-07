-- Prove2me | Theorems.Thm_RefWPHP_lemma_3_1
-- name    : RefWPHP.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:09:48.972189+00:00
-- url     : https://prove2.me/theorems/f7d774ed-b212-4253-a4f4-6ba5c89841d7
-- title:
--   Lemma 3.1 — correctness of the reduction within PK$_2$: $\mathrm{PHP}^L_W \vdash_{\mathrm{PK}_2} \mathrm{Ref}_s(\varphi){\restriction}\sigma_{\pi,s}$ in polynomial size
-- statement:
--   Let $\varphi$ be a CNF over $n$ variables with $m$ clauses, $\pi$ a layered Resolution refutation of $\varphi$ with parameters $L$ and $D$, and $s \in \mathbb N$ with $D \le s < L$. Put $W = \lfloor s/D\rfloor$. Then $\sigma_{\pi,s}$ is a depth-2 substitution, and there is one PK$_2$-derivation from $\mathrm{PHP}^L_W$ that contains the cedent $\Gamma{\restriction}\sigma_{\pi,s}$ for every clause $\Gamma$ of $\mathrm{Ref}_s(\varphi)$, and has size
--
--   $$
--   \le (L + D + s + n + m + 2)^{c_0},
--   $$
--
--   where $c_0$ is an absolute constant, fixed before all the data.
--
--   This lemma is the first half of the reduction: from the pigeonhole axioms one obtains every substituted axiom of $\mathrm{Ref}_s(\varphi)$ at polynomial cost.
--
--   Differences from the source:
--   - reading: in total size poly(L, D, s, n, m) → derivSize at most (L + D + s + n + m + 2)^c₀ with c₀ fixed before all data; reason: the page's bound is uniform in φ and π, and this is the stronger reading of poly
--   - encoding: size is the length of a binary string (p.15) → symbol count plus one per line (derivSize); reason: the two differ by at most a logarithmic factor in the number of variables, which the polynomial absorbs
--   - encoding: a-lit^A_ℓ occur in (Ref-3) → they are constants: (Ref-3) only for ℓ ∈ C_A, without the literal; reason: p.22 fixes them as constants for a fixed φ; the omitted instances are satisfied
--   - reading: a PK_2-derivation of the form PHP ⊢ Ref↾σ → one derivation whose lines include Γ↾σ for every clause Γ of Ref_s(φ), plus the bound depth (σ x) ≤ 2 as a first conjunct; reason: the proof derives every instance of (Ref-1) to (Ref-11) under σ, and the statement names σ as depth-2
--   - reading: (3.1b), (3.1c): P^left_{k,b,c}, P^right_{k,b,c} range over C ∈ π_k → they range over the derived C ∈ π_k; reason: left_π(C) and right_π(C) exist only for derived C
--   - encoding: grid B_{k,b} with leftover blocks in the last layer and otherwise unspecified numbering; leftover variables may be set to ⊥ or any other value (p.20) → B_{k,b} has index (D−1−k)·W + b, indices D·W … s−1 are leftover with every variable ↦ ⊥; reason: the pointer variables require B_{k+1,c} < B_{k,b}, and p.20 leaves the choice free
--   - encoding: clauses of Ref_s(φ) and PHP are written with → and ⋁ → each clause is the cedent of its literals; reason: p.15 collects a CNF into a set of cedents, and PK_0 must be Resolution; no instance changes
--   - reading: binary ∧-Intro and ∨-Intro on unbounded fan-in formulas, used in one step as "repeated ∧-introduction"; Cut on φ₁ ∧ ⋯ ∧ φ_m; cedents are sequences → PKStep: n-ary ∧/∨-introduction (0-ary ∧ gives ⊤), Atomic LEM, weakening to any list containing the premise, Cut on one formula and on a conjunction, hypotheses from Φ; dag-like lines; reason: ⊤ and ⊥ occur as formulas in (3.2)–(3.3), PK_0 must be Resolution (p.15), and the page counts repeated introductions as one step
--   - reading: logical axioms x ∨ ¬x are allowed as leaves (p.14), and the root is the final inference over a variable (p.20) → leaves are weakenings of clauses of φ, and the root is a resolution over x_{i∅}; reason: the proof of (3.23), p.23, uses that an underived clause weakens an axiom of φ; tautological clauses can be removed without changing layers, L or D, so this reading is not weaker
--   - generalization: π is a layered refutation of length L in which every root-to-leaf path has length exactly D (p.19) → LayeredRef φ L D: L bounds each layer, leaves may sit in any layer, a resolvent need only contain the union of the reduced premises; reason: the page's π is an instance (each layer has at most length(π) clauses, and a leaf at layer D is a leaf); the argument never uses the exact form
--   - encoding: layers k ∈ [D] and blocks in [s+1], with the root as block s+1 → layer k : Fin D is the paper's π_{k+1}, blocks are Fin (s+1), the root is Fin.last s, and LayeredRef requires 0 < D; reason: Lean indexing; W = ⌊s/D⌋ and the root's premises in π_1 presuppose D ≥ 1; no instance changes
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), Lemma 3.1, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_phpCNF
import Definitions.Def_RefWPHP_LayeredRef
import Definitions.Def_RefWPHP_refCNF
import Definitions.Def_RefWPHP_sigma

namespace RefWPHP

open PKFormula

/-- Lemma 3.1 (Correctness of the reduction within PK_2), p.20 (PDF 22), of N. Arteche,
*Resolution Lower Bounds versus the Weak Pigeonhole Principle*, STOC 2027 submission (held
manuscript, sha256 ee75d7f1…): for a CNF `φ` over `n` variables and `m` clauses with a layered
Resolution refutation `π` of length `L` and depth `D`, and every `s` with `D ≤ s < L`, there is a
PK_2-derivation `PHP^L_W ⊢_{PK_2} Ref_s(φ)↾σ_{π,s}` in total size `poly(L, D, s, n, m)`, where
`σ_{π,s}` is the depth-2 substitution of (3.2)–(3.3) and `W = ⌊s/D⌋`.

**Formalization Note.** One derivation contains every cedent of `Ref_s(φ)` with `σ_{π,s}` applied.
"poly" is `(L + D + s + n + m + 2)^c₀` with `c₀` fixed before every object. "Depth-2" is the first
conjunct. -/
theorem lemma_3_1 : ∃ c₀ : ℕ, ∀ {n m : ℕ} (φ : Fin m → Finset (Lit n)) {L D : ℕ}
    (π : LayeredRef φ L D) (s : ℕ), D ≤ s → s < L →
    (∀ x : RefVar n m s, depth (sigma π s x) ≤ 2) ∧
    ∃ ρ : List (Cedent (Fin L × Fin (s / D))),
      IsPKDerivation 2 (phpCNF L (s / D)) ρ ∧
      (∀ Γ ∈ refCNF φ s, Γ.map (subst (sigma π s)) ∈ ρ) ∧
      derivSize ρ ≤ (L + D + s + n + m + 2) ^ c₀ := by sorry

end RefWPHP
