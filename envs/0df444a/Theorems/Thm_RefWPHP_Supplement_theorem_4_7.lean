-- Prove2me | Theorems.Thm_RefWPHP_Supplement_theorem_4_7
-- name    : RefWPHP.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:28:10.457798+00:00
-- url     : https://prove2.me/theorems/eab0c98d-3efd-494a-904d-28f9a375f1bd
-- title:
--   Theorem 4.7 — under Hypothesis 1.9, every $\mathrm{Res}(k)$ refutation of $\mathrm{Ref}_s(\varphi)$ with $s \ge n^C$ has size $\ge 2^{(s/n)^\gamma}$
-- statement:
--   Assume Hypothesis 1.9. Then for every $k \in \mathbb N$ there are constants $C = C(k) \in \mathbb N$ and $\gamma = \gamma(k) > 0$, and a threshold $n_0 = n_0(k)$, such that for every unsatisfiable CNF formula $\varphi$ over $n \ge n_0$ variables (with any number of clauses) and every $s \ge n^C$, every $\mathrm{Res}(k)$-refutation of $\mathrm{Ref}_s(\varphi)$ has size at least
--
--   $$
--   2^{(s/n)^{\gamma}} .
--   $$
--
--   This is a conditional analogue, for $k$-DNF Resolution, of the $2^{\Omega(s/n)}$ lower bound of Atserias and Müller for Resolution refutations of $\mathrm{Ref}_s(\varphi)$. It is the basis of Theorem 4.10 (the Iterated Lower Bound Hypothesis for $\mathrm{Res}(k)$).
--
--   **Formalization Note** The hypothesis is the argument `h : OntoWPHPHypothesis`. $\mathrm{Res}(k)$ is $\mathrm{PK}^k_0$ (`IsPKkRefutation k 0`); size is the base `derivSize`.
--
--   Differences from the source:
--   - encoding: Assume Hypothesis 1.9 → hypothesis h : OntoWPHPHypothesis; reason: "Assume" is an implication
--   - generalization: every k ∈ ℕ, with Res(k) defined for k ≥ 1 (Res(1) = Resolution, p.15, p.40) → every k : ℕ, k = 0 meaning PK^0_0; reason: a PK^0_0-refutation is a PK^1_0-refutation, so the extra case k = 0 follows from k = 1 and the statement specializes to the source's
--   - encoding: constant C = C(k) → C : ℕ; reason: a larger C only weakens the claim, so a real C can be rounded up
--   - reading: PK^k_d: formulas of depth d + 1 whose gates "at depth d" have fan-in at most k; Res(k) = PK^k_0 (p.15) → IsPKkRefutation k 0: base PKStep lines whose formulas have depth ≤ 1 and whose root gates have at most k arguments; reason: a gate's depth is read as its distance from the root, the only reading under which d = 0 constrains anything; a top-level disjunction of at most k literals is the same as listing them in the cedent
--   - encoding: an unsatisfiable CNF over n variables and m clauses → φ : Fin m → Finset (Lit n) with Unsat φ; n counts every variable, m counts clauses with repetition; reason: the base mission's representation of CNFs; no instance changes
--   - encoding: size is the length of a binary string (p.15); "in size T" → derivSize, the symbol count plus one per line; size at most T; reason: the two sizes differ by at most a logarithmic factor in the number of variables, which every bound in the statement absorbs (base mission convention)
--   - encoding: the variables a-lit^A_ℓ of Ref_s(φ) → constants 1{ℓ ∈ C_A}: (Ref-3) only for ℓ ∈ C_A, without that literal; reason: p.22 fixes them as constants for a fixed φ; the omitted instances are satisfied (base mission's refCNF)
--   - encoding: CNF clauses (of φ, Ref_s(φ), PHP, ontoPHP) written with → and ⋁ → each clause is the cedent of its literals; reason: p.15 collects a CNF into a set of cedents; no instance changes (base mission convention)
--   - reading: binary ∧/∨-Intro used as "repeated ∧-introduction", Cut on φ₁ ∧ ⋯ ∧ φ_m, cedents as sequences → the base PKStep: n-ary ∧/∨-introduction, Atomic LEM, weakening to any list containing the premise, Cut on one formula and on a conjunction, hypotheses; dag-like lines; reason: the base mission's published calculus; ⊤ and ⊥ are formulas there and PK_0 is Resolution (p.15)
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), Theorem 4.7, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_refCNF
import Definitions.Def_RefWPHP_Supplement_Unsat
import Definitions.Def_RefWPHP_Supplement_IsPKkDerivation
import Definitions.Def_RefWPHP_Supplement_OntoWPHPHypothesis

namespace RefWPHP

namespace Supplement

/-- Theorem 4.7, p.36 (PDF 38), of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole
Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…): "Assume Hypothesis 1.9. For
every `k ∈ ℕ` there exist constants `C = C(k)` and `γ = γ(k) > 0` such that for every unsatisfiable
CNF formula `φ` over a sufficiently large number `n` of variables and every `s ≥ n^C`, it holds that
every `Res(k)`-refutation of `Ref_s(φ)` has size at least `2^{(s/n)^γ}`."

**Formalization Note.** Hypothesis 1.9 is the hypothesis `h`, not an axiom. `Res(k)` is `PK^k_0`
(`IsPKkRefutation k 0`), size the base `derivSize`. `C` is a natural number and `γ` a positive real,
both chosen after `k` only; the threshold `n₀` also depends on `k` only. The number `m` of clauses
is arbitrary. For `k = 0` the claim follows from `k = 1`. -/
theorem theorem_4_7 (h : OntoWPHPHypothesis) : ∀ k : ℕ, ∃ C : ℕ, ∃ γ : ℝ, 0 < γ ∧ ∃ n₀ : ℕ,
    ∀ {n m : ℕ} (φ : Fin m → Finset (Lit n)), n₀ ≤ n → Unsat φ → ∀ s : ℕ, n ^ C ≤ s →
      ∀ ρ : List (Cedent (RefVar n m s)), IsPKkRefutation k 0 (refCNF φ s) ρ →
        (2 : ℝ) ^ (((s : ℝ) / n) ^ γ) ≤ (derivSize ρ : ℝ) := by sorry

end Supplement

end RefWPHP
