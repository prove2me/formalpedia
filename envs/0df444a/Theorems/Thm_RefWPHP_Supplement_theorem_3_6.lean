-- Prove2me | Theorems.Thm_RefWPHP_Supplement_theorem_3_6
-- name    : RefWPHP.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:26:19.665804+00:00
-- url     : https://prove2.me/theorems/20bd6a2f-5219-4bcd-8f72-697fc16caea7
-- title:
--   Theorem 3.6 — $\mathrm{Res}(k)$ refutations of $\mathrm{Ref}_s(\varphi)$ give $\mathrm{Res}(2k)$ refutations of $\mathrm{ontoPHP}^L_{\lfloor s/D\rfloor}$, size $T \cdot \mathrm{poly} \cdot L^{O(k)}$
-- statement:
--   Let $\varphi$ be a CNF formula over $n$ variables with $m$ clauses that admits a layered Resolution refutation $\pi$ of length $L$ and depth $D$. For all $k \ge 1$ and $s$ with $D \le s < L$, and with $W = \lfloor s/D \rfloor$: if $\mathrm{Ref}_s(\varphi)$ has a $\mathrm{Res}(k)$-refutation of size at most $T$, then $\mathrm{ontoPHP}^L_W$ has a $\mathrm{Res}(2k)$-refutation of size at most
--
--   $$
--   T \cdot (L + D + s + n + m + 2)^{c} \cdot (L + 2)^{c k},
--   $$
--
--   where the exponent $c$ is an absolute constant, fixed before $\varphi$, $\pi$, $k$, $s$ and $T$.
--
--   This is the $\mathrm{Res}(k)$ version of the paper's main reduction (Theorem 3.2): at the price of the onto axioms and of doubling the width of the DNFs, the depth of the lines does not grow. It is the input to Theorem 4.7.
--
--   **Formalization Note** $\mathrm{Res}(k)$ is $\mathrm{PK}^k_0$ (`IsPKkRefutation k 0`), $\mathrm{Ref}_s(\varphi)$ is the base `refCNF φ s`, and $\pi$ is the base `LayeredRef φ L D`, exactly as in Theorem 3.2.
--
--   Differences from the source:
--   - reading: k ∈ ℕ → 1 ≤ k; reason: Res(k) is defined for k ≥ 2 and Res(1) = PK^1_0 is Resolution (p.15, p.40); the paper has no system Res(0)
--   - reading: T · poly(L, D, s, n, m) · L^{O(k)} → T · (L + D + s + n + m + 2)^c · (L + 2)^{c·k} with one c fixed before φ, π, k, s, T; reason: the O(k) of the proof (Lemma 3.4's M^{O(k)} with M = O(L²)) and its poly have absolute constants; L ≥ 2 here (1 ≤ D ≤ s < L), so (L + 2)^{ck} ≤ L^{2ck}
--   - reading: PK^k_d: formulas of depth d + 1 whose gates "at depth d" have fan-in at most k; Res(k) = PK^k_0 (p.15) → IsPKkRefutation k 0: base PKStep lines whose formulas have depth ≤ 1 and whose root gates have at most k arguments; reason: a gate's depth is read as its distance from the root, the only reading under which d = 0 constrains anything; a top-level disjunction of at most k literals is the same as listing them in the cedent
--   - encoding: size is the length of a binary string (p.15); "in size T" → derivSize, the symbol count plus one per line; size at most T; reason: the two sizes differ by at most a logarithmic factor in the number of variables, which every bound in the statement absorbs (base mission convention)
--   - encoding: the variables a-lit^A_ℓ of Ref_s(φ) → constants 1{ℓ ∈ C_A}: (Ref-3) only for ℓ ∈ C_A, without that literal; reason: p.22 fixes them as constants for a fixed φ; the omitted instances are satisfied (base mission's refCNF)
--   - encoding: CNF clauses (of φ, Ref_s(φ), PHP, ontoPHP) written with → and ⋁ → each clause is the cedent of its literals; reason: p.15 collects a CNF into a set of cedents; no instance changes (base mission convention)
--   - reading: binary ∧/∨-Intro used as "repeated ∧-introduction", Cut on φ₁ ∧ ⋯ ∧ φ_m, cedents as sequences → the base PKStep: n-ary ∧/∨-introduction, Atomic LEM, weakening to any list containing the premise, Cut on one formula and on a conjunction, hypotheses; dag-like lines; reason: the base mission's published calculus; ⊤ and ⊥ are formulas there and PK_0 is Resolution (p.15)
--   - encoding: φ is a CNF that admits a layered refutation → no unsatisfiability hypothesis; reason: LayeredRef φ L D implies it (as in the base goal)
--   - reading: logical axioms x ∨ ¬x allowed as leaves (p.14); the root is the final inference over a variable (p.20) → leaves are weakenings of clauses of φ; the root is a resolution over x_{i∅}; reason: the base mission's LayeredRef; tautological leaves can be removed without changing layers, L or D
--   - generalization: π layered of length L, every root-to-leaf path of length exactly D (p.19) → LayeredRef φ L D: L bounds each layer, leaves may sit in any layer, a resolvent need only contain the union of the reduced premises; reason: the page's π is an instance (each layer has at most length(π) clauses), so the Lean statement specializes to the source's
--   - encoding: layers in [D], blocks in [s+1] with the root block s+1 → layers Fin D, blocks Fin (s+1), root Fin.last s, 0 < D; reason: Lean indexing (base mission convention); no instance changes
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), Theorem 3.6, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_LayeredRef
import Definitions.Def_RefWPHP_refCNF
import Definitions.Def_RefWPHP_Supplement_ontoPhpCNF
import Definitions.Def_RefWPHP_Supplement_IsPKkDerivation

namespace RefWPHP

namespace Supplement

/-- Theorem 3.6, p.34 (PDF 36), of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole
Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…): "Let `φ` be a CNF formula over
`n` variables and `m` clauses that admits a layered Resolution refutation `π` of length `L` and depth
`D`. For every `k, s ∈ ℕ` such that `D ≤ s < L`, if `Ref_s(φ)` admits a `Res(k)`-refutation of size
`T`, then `ontoPHP^L_W` admits a `Res(2k)`-refutation of size at most
`T · poly(L, D, s, n, m) · L^{O(k)}`, where `W ≔ ⌊s/D⌋`."

**Formalization Note.**
1. `Res(k)` is `PK^k_0` (`IsPKkRefutation k 0`) over the base calculus `PKStep`; size is the base
   `derivSize`, and "of size `T`" is "of size at most `T`".
2. "`T · poly(L, D, s, n, m) · L^{O(k)}`" is `T · (L + D + s + n + m + 2)^c · (L + 2)^{c·k}` with one
   exponent `c` fixed before every object, `k` included.
3. `k ≥ 1`: `Res(k)` is defined for `k ≥ 2`, and `Res(1)` (`PK^1_0`) is Resolution (p.15, p.40).
4. The layered refutation `π` is the base mission's `LayeredRef φ L D`, as in Theorem 3.2. -/
theorem theorem_3_6 : ∃ c : ℕ, ∀ {n m : ℕ} (φ : Fin m → Finset (Lit n)) {L D : ℕ}
    (π : LayeredRef φ L D) (k s T : ℕ), 1 ≤ k → D ≤ s → s < L →
    (∃ ρ : List (Cedent (RefVar n m s)), IsPKkRefutation k 0 (refCNF φ s) ρ ∧ derivSize ρ ≤ T) →
    ∃ ρ' : List (Cedent (Fin L × Fin (s / D))),
      IsPKkRefutation (2 * k) 0 (ontoPhpCNF L (s / D)) ρ' ∧
      derivSize ρ' ≤ T * (L + D + s + n + m + 2) ^ c * (L + 2) ^ (c * k) := by sorry

end Supplement

end RefWPHP
