-- Prove2me | Theorems.Thm_RefWPHP_Supplement_theorem_4_5
-- name    : RefWPHP.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:27:30.63421+00:00
-- url     : https://prove2.me/theorems/db0a8f53-2dd2-4b71-8cd7-884d0d59c0aa
-- title:
--   Theorem 4.5 — under the WPHP Hypothesis, PK$_d$ lacks polynomial-size refutations of naturally tight and of maximally hard Resolution lower bounds
-- statement:
--   Assume the WPHP Hypothesis (Hypothesis 1.4) and let $d \in \mathbb N$.
--
--   1. Let $\varphi = \{\varphi_n\}$ be a family of CNF formulas, $\varphi_n$ with $N(n)$ variables and $M(n)$ clauses, that admits a naturally tight Resolution lower bound $s = s(n)$ (Definition 4.3). Then for every $k \in \mathbb N$ there is $n_0$ such that for every $n \ge n_0$, every $\mathrm{PK}_d$-refutation of $\mathrm{Ref}_{s(n)}(\varphi_n)$ has size
--   $$
--   > s(n)^k .
--   $$
--   2. In particular, let $\varphi = \{\varphi_n\}$, $\varphi_n$ with $n$ variables, be maximally hard for Resolution with constant $\varepsilon > 0$ (Definition 4.2: refutations of length $\ge 2^{\varepsilon n}$ for large $n$). Then for every $k$ there is $n_0$ such that for every $n \ge n_0$, every $\mathrm{PK}_d$-refutation of $\mathrm{Ref}_{\lfloor 2^{\varepsilon n}\rfloor}(\varphi_n)$ has size $> \lfloor 2^{\varepsilon n} \rfloor^k$.
--
--   In the paper's words, $\mathrm{PK}_d$ lacks polynomial-size refutations of the statements $\{\mathrm{Ref}_{s(n)}(\varphi_n)\}$ expressing the lower bound. Corollary 4.6 applies this to the pigeonhole formulas $\mathrm{PHP}^{n+1}_n$.
--
--   **Formalization Note** Definitions 4.3 and 4.2 are `IsNaturallyTight` and `IsMaximallyHard`. The size of $\mathrm{Ref}_{s(n)}(\varphi_n)$ is polynomial in $s(n)$, because $N(n), M(n) \le \mathrm{poly}(n)$ and $s(n) \ge n^{\Omega(1)}$, so a bound $> s(n)^k$ for every $k$ excludes refutations of size polynomial in the size of the formula.
--
--   Differences from the source:
--   - generalization: PK_d lacks polynomial-size refutations of {Ref_{s(n)}(φ_n)} → for every k, for all large n, every PK_d-refutation of Ref_{s(n)}(φ_n) has size > s(n)^k; reason: |Ref_{s(n)}(φ_n)| ≤ poly(s(n)) since N, M ≤ poly(n) and n ≤ s(n)^{O(1)}, so the eventual bound for every k implies that no polynomial in the formula size bounds the refutations for all n; it is what the proof gives
--   - reading: PK_d lacks polynomial-size refutations of 2^{Ω(n)} lower bounds for maximally hard formulas → for every ε with IsMaximallyHard M φ ε, the statements Ref_{⌊2^{εn}⌋}(φ_n), with the bound of clause 1; reason: the statement expressing the lower bound 2^{εn} is Ref_{⌊2^{εn}⌋}(φ_n)
--   - encoding: poly(n), s(n) ≥ n^{Ω(1)}, 2^{Ω(n)}, "for every large enough n" in Definitions 4.2 and 4.3 → ≤ (n + 2)^a; ∃ b > 0, n₁ with n^b ≤ s(n) for n ≥ n₁; ∃ ε > 0 with length ≥ 2^{εn}; ∃ n₀; reason: the standard meaning of the asymptotic notation
--   - encoding: Resolution refutations with length and depth (pp.13–14) → ResRefutation, whose lines carry their justifications; depth ≤ D via a labelling of the lines; reason: depth is a property of the dag; the labelling form is equivalent to the longest-path definition
--   - encoding: Assume the WPHP Hypothesis (Hypothesis 1.4) → hypothesis hW : WPHPHypothesis; reason: "Assume" is an implication
--   - encoding: size is the length of a binary string (p.15); "in size T" → derivSize, the symbol count plus one per line; size at most T; reason: the two sizes differ by at most a logarithmic factor in the number of variables, which every bound in the statement absorbs (base mission convention)
--   - encoding: the variables a-lit^A_ℓ of Ref_s(φ) → constants 1{ℓ ∈ C_A}: (Ref-3) only for ℓ ∈ C_A, without that literal; reason: p.22 fixes them as constants for a fixed φ; the omitted instances are satisfied (base mission's refCNF)
--   - encoding: CNF clauses (of φ, Ref_s(φ), PHP, ontoPHP) written with → and ⋁ → each clause is the cedent of its literals; reason: p.15 collects a CNF into a set of cedents; no instance changes (base mission convention)
--   - reading: binary ∧/∨-Intro used as "repeated ∧-introduction", Cut on φ₁ ∧ ⋯ ∧ φ_m, cedents as sequences → the base PKStep: n-ary ∧/∨-introduction, Atomic LEM, weakening to any list containing the premise, Cut on one formula and on a conjunction, hypotheses; dag-like lines; reason: the base mission's published calculus; ⊤ and ⊥ are formulas there and PK_0 is Resolution (p.15)
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), Theorem 4.5, p.36 (PDF p.38); Definitions 4.2, 4.3, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_refCNF
import Definitions.Def_RefWPHP_Supplement_WPHPHypothesis
import Definitions.Def_RefWPHP_Supplement_IsNaturallyTight
import Definitions.Def_RefWPHP_Supplement_IsMaximallyHard

namespace RefWPHP

namespace Supplement

/-- Theorem 4.5, p.36 (PDF 38), of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole
Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…): "Assume the WPHP Hypothesis
holds (Hypothesis 1.4). For every `d ∈ ℕ` and every sequence `φ = {φ_n}` admitting a naturally tight
Resolution lower bound of size `s = s(n)`, it holds that `PK_d` lacks polynomial-size refutations of
the statements `{Ref_s(φ_n)}` stating such a lower bound. In particular, `PK_d` lacks
polynomial-size refutations of `2^{Ω(n)}` lower bounds for maximally hard formulas for Resolution."

The two clauses are the two conjuncts.

**Formalization Note.**
1. "`PK_d` lacks polynomial-size refutations of `{Ref_{s(n)}(φ_n)}`" is read as: for every `k`, for
   all large `n`, every `PK_d`-refutation of `Ref_{s(n)}(φ_n)` has size `> s(n)^k`. Size is measured
   in `s(n)`, which is polynomially related to the size of `Ref_{s(n)}(φ_n)` since `φ_n` has
   `poly(n)` variables and clauses and `s(n) ≥ n^{Ω(1)}`; "for all large `n`" is stronger than the
   negation of "polynomial-size for every `n`".
2. In the second clause the lower bound `2^{Ω(n)}` is `2^{εn}` for a constant `ε` witnessing maximal
   hardness, and the statement refuted is `Ref_{⌊2^{εn}⌋}(φ_n)`. -/
theorem theorem_4_5 (hW : WPHPHypothesis) :
    (∀ (d : ℕ) (N M : ℕ → ℕ) (φ : (n : ℕ) → Fin (M n) → Finset (Lit (N n))) (s : ℕ → ℕ),
      IsNaturallyTight N M φ s → ∀ k : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ ρ : List (Cedent (RefVar (N n) (M n) (s n))),
          IsPKRefutation d (refCNF (φ n) (s n)) ρ → s n ^ k < derivSize ρ) ∧
    (∀ (d : ℕ) (M : ℕ → ℕ) (φ : (n : ℕ) → Fin (M n) → Finset (Lit n)) (ε : ℝ),
      IsMaximallyHard M φ ε → ∀ k : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ ρ : List (Cedent (RefVar n (M n) ⌊(2 : ℝ) ^ (ε * n)⌋₊)),
          IsPKRefutation d (refCNF (φ n) ⌊(2 : ℝ) ^ (ε * n)⌋₊) ρ →
            ⌊(2 : ℝ) ^ (ε * n)⌋₊ ^ k < derivSize ρ) := by sorry

end Supplement

end RefWPHP
