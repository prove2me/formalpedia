-- Prove2me | Theorems.Thm_RefWPHP_theorem_3_2
-- name    : RefWPHP.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:04:30.691909+00:00
-- url     : https://prove2.me/theorems/50cecb37-fedf-4297-905a-8f95b6248579
-- title:
--   Theorem 3.2 — a size-$T$ PK$_d$ refutation of $\mathrm{Ref}_s(\varphi)$ gives a PK$_{d+2}$ refutation of $\mathrm{PHP}^L_{\lfloor s/D\rfloor}$ of size $T\cdot\mathrm{poly}(L,D,s,n,m)$
-- statement:
--   Let $\varphi$ be an unsatisfiable CNF over $n$ variables with $m$ clauses that admits a layered Resolution refutation $\pi$ in length $L$ and depth $D$, and let $d \in \mathbb N$. For every $s \in \mathbb N$ with $D \le s < L$, and with $W = \lfloor s/D\rfloor$: if PK$_d$ refutes $\mathrm{Ref}_s(\varphi)$ in size $T$, then PK$_{d+2}$ refutes $\mathrm{PHP}^L_W$ in size
--
--   $$
--   \le T \cdot (L + D + s + n + m + 2)^{c},
--   $$
--
--   where the exponent $c$ is an absolute constant, fixed before $\varphi$, $\pi$, $d$, $s$ and $T$.
--
--   This is the central contribution of the paper: a constant-depth Frege proof of a Resolution length lower bound yields a constant-depth Frege proof of a weak pigeonhole principle at polynomial overhead in size. The blow-up is linear in $T$ and the depth grows by exactly $2$.
--
--   Differences from the source:
--   - reading: T · poly(L, D, s, n, m) → T · (L + D + s + n + m + 2)^c with one c fixed before φ, π, d, s, T; reason: the proof's blow-up comes from σ_{π,s}, which does not depend on d; this is the stronger reading of poly
--   - encoding: size is the length of a binary string (p.15); in size T → symbol count plus one per line (derivSize); size at most T; reason: the two sizes differ by at most a logarithmic factor in the number of variables, which the polynomial absorbs
--   - encoding: φ is unsatisfiable → no separate hypothesis; reason: LayeredRef φ L D implies it
--   - encoding: a-lit^A_ℓ occur in (Ref-3) → they are constants: (Ref-3) only for ℓ ∈ C_A, without the literal; reason: p.22 fixes them as constants for a fixed φ; the omitted instances are satisfied
--   - encoding: clauses of Ref_s(φ) and PHP are written with → and ⋁ → each clause is the cedent of its literals; reason: p.15 collects a CNF into a set of cedents, and PK_0 must be Resolution; no instance changes
--   - reading: binary ∧-Intro and ∨-Intro on unbounded fan-in formulas, used in one step as "repeated ∧-introduction"; Cut on φ₁ ∧ ⋯ ∧ φ_m; cedents are sequences → PKStep: n-ary ∧/∨-introduction (0-ary ∧ gives ⊤), Atomic LEM, weakening to any list containing the premise, Cut on one formula and on a conjunction, hypotheses from Φ; dag-like lines; reason: ⊤ and ⊥ occur as formulas in (3.2)–(3.3), PK_0 must be Resolution (p.15), and the page counts repeated introductions as one step
--   - reading: logical axioms x ∨ ¬x are allowed as leaves (p.14), and the root is the final inference over a variable (p.20) → leaves are weakenings of clauses of φ, and the root is a resolution over x_{i∅}; reason: the proof of (3.23), p.23, uses that an underived clause weakens an axiom of φ; tautological clauses can be removed without changing layers, L or D, so this reading is not weaker
--   - generalization: π is a layered refutation of length L in which every root-to-leaf path has length exactly D (p.19) → LayeredRef φ L D: L bounds each layer, leaves may sit in any layer, a resolvent need only contain the union of the reduced premises; reason: the page's π is an instance (each layer has at most length(π) clauses, and a leaf at layer D is a leaf); the argument never uses the exact form
--   - encoding: layers k ∈ [D] and blocks in [s+1], with the root as block s+1 → layer k : Fin D is the paper's π_{k+1}, blocks are Fin (s+1), the root is Fin.last s, and LayeredRef requires 0 < D; reason: Lean indexing; W = ⌊s/D⌋ and the root's premises in π_1 presuppose D ≥ 1; no instance changes
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), Theorem 3.2, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_phpCNF
import Definitions.Def_RefWPHP_LayeredRef
import Definitions.Def_RefWPHP_refCNF

namespace RefWPHP

/-- Theorem 3.2, p.26 (PDF 28), of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole
Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…): "Let `φ` be an
unsatisfiable CNF formula over `n` variables and `m` clauses that admits a layered Resolution
refutation `π` in length `L` and depth `D`, and let `d ∈ ℕ`. For every `s ∈ ℕ` such that
`D ≤ s < L`, if PK_d admits a refutation of `Ref_s(φ)` in size `T`, then PK_{d+2} admits a
refutation of `PHP^L_W` in size `T · poly(L, D, s, n, m)`, where `W = ⌊s/D⌋`."

**Formalization Note.**
1. "`T · poly(L, D, s, n, m)`" is `T · (L + D + s + n + m + 2)^c` with one exponent `c` fixed
   before every object, including `d`.
2. Size is the symbol count of the derivation plus one per line (`derivSize`), and "in size `T`"
   is "of size at most `T`".
3. The calculus is `PKStep` (n-ary ∧/∨-introduction, atomic LEM, weakening, cut on a formula and
   on a conjunction, hypotheses); derivations are dag-like.
4. Unsatisfiability of `φ` follows from `π`, so it is not a separate hypothesis. -/
theorem theorem_3_2 : ∃ c : ℕ, ∀ {n m : ℕ} (φ : Fin m → Finset (Lit n)) {L D : ℕ}
    (π : LayeredRef φ L D) (d s T : ℕ), D ≤ s → s < L →
    (∃ ρ : List (Cedent (RefVar n m s)), IsPKRefutation d (refCNF φ s) ρ ∧ derivSize ρ ≤ T) →
    ∃ ρ' : List (Cedent (Fin L × Fin (s / D))),
      IsPKRefutation (d + 2) (phpCNF L (s / D)) ρ' ∧
      derivSize ρ' ≤ T * (L + D + s + n + m + 2) ^ c := by sorry

end RefWPHP
