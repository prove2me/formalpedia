-- Prove2me | Theorems.Thm_RefWPHP_Supplement_theorem_6_7
-- name    : RefWPHP.Supplement.theorem_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:29:25.795202+00:00
-- url     : https://prove2.me/theorems/daacc967-cbd8-44d9-9469-b97989de1881
-- title:
--   Theorem 6.7 — there are formulas $\gamma_n$ such that polynomial-size PK$_d$ refutations of $\mathrm{PHP}^{m^2}_m$ give polynomial-size PK$_{d+O(1)}$ refutations of $\mathrm{Ref}_{n^k}(\gamma_n)$
-- statement:
--   There are a family $\{\gamma_n\}_{n \in \mathbb N}$ of unsatisfiable CNF formulas, $\gamma_n$ with $N(n) \le (n+2)^a$ variables and $M(n) \le (n+2)^a$ clauses for some exponent $a$, and a constant $c \in \mathbb N$, such that for all $k, d \in \mathbb N$ the following holds. If $\mathrm{PK}_d$ admits polynomial-size refutations of $\{\mathrm{PHP}^{m^2}_m\}_{m}$, that is, for some $e$ and all large $m$ a $\mathrm{PK}_d$-refutation of $\mathrm{PHP}^{m^2}_m$ of size at most $m^e$, then for some $e'$ and all large $n$ there is a refutation
--
--   $$
--   \mathrm{PK}_{d+c} \vdash \neg\,\mathrm{Ref}_{n^k}(\gamma_n) \quad\text{of size at most } n^{e'} .
--   $$
--
--   Moreover, unconditionally, for every $k$ the formulas $\mathrm{Ref}_{n^k}(\gamma_n)$ are unsatisfiable for all large $n$ (every assignment to their variables falsifies one of their clauses).
--
--   So polynomial lower bounds $n^k$ for Resolution are provable at constant depth from the weak pigeonhole principle; if the WPHP Hypothesis fails, these Resolution lower bounds have polynomial-size constant-depth Frege proofs (Pudlák's problem).
--
--   **Formalization Note** The depth increment $O(1)$ is the single constant $c$, chosen after the family and before $k$ and $d$. $\mathrm{PK}_d$ is the base `IsPKRefutation d`, $\mathrm{PHP}^{m^2}_m$ the base `phpCNF (m^2) m`, and $\mathrm{Ref}_{n^k}(\gamma_n)$ the base `refCNF (γ n) (n^k)`.
--
--   Differences from the source:
--   - reading: PK_{d+O(1)} → PK_{d+c} with one c chosen after the family and before k and d; reason: the proof's increment (stretch amplification to the fixed stretch of Theorem 6.6, the PK_{d+1+1/2} step and the depth-2 definitions of π′) depends on neither k nor d; this is the stronger reading
--   - reading: PK_d admits polynomial-size refutations of {PHP^{m²}_m} → ∃ e m₀, ∀ m ≥ m₀, a PK_d-refutation of size ≤ m^e; reason: PHP^1_1 is satisfiable, so "for every m" would make the hypothesis vacuous; requiring only large m weakens the hypothesis and so strengthens the theorem; the size of PHP^{m²}_m is polynomial in m
--   - reading: PK_{d+O(1)} admits polynomial-size refutations of the unsatisfiable formulas {Ref_{n^k}(γ_n)} → the unconditional conjunct ∀ k, ∃ n₀, ∀ n ≥ n₀, Ref_{n^k}(γ_n) unsatisfiable, and ∃ e' n₀, ∀ n ≥ n₀, a PK_{d+c}-refutation of Ref_{n^k}(γ_n) of size ≤ n^{e'}; reason: for small n, Ref_{n^k}(γ_n) can be satisfiable (γ_n may have a refutation of length ≤ n^k), so the page's "unsatisfiable" holds for large n; the size of Ref_{n^k}(γ_n) is polynomial in n
--   - encoding: poly(n) variables and poly(n) clauses → N n ≤ (n + 2)^a and M n ≤ (n + 2)^a for one a; reason: the standard meaning of poly(n)
--   - encoding: size is the length of a binary string (p.15); "in size T" → derivSize, the symbol count plus one per line; size at most T; reason: the two sizes differ by at most a logarithmic factor in the number of variables, which every bound in the statement absorbs (base mission convention)
--   - encoding: the variables a-lit^A_ℓ of Ref_s(φ) → constants 1{ℓ ∈ C_A}: (Ref-3) only for ℓ ∈ C_A, without that literal; reason: p.22 fixes them as constants for a fixed φ; the omitted instances are satisfied (base mission's refCNF)
--   - encoding: CNF clauses (of φ, Ref_s(φ), PHP, ontoPHP) written with → and ⋁ → each clause is the cedent of its literals; reason: p.15 collects a CNF into a set of cedents; no instance changes (base mission convention)
--   - reading: binary ∧/∨-Intro used as "repeated ∧-introduction", Cut on φ₁ ∧ ⋯ ∧ φ_m, cedents as sequences → the base PKStep: n-ary ∧/∨-introduction, Atomic LEM, weakening to any list containing the premise, Cut on one formula and on a conjunction, hypotheses; dag-like lines; reason: the base mission's published calculus; ⊤ and ⊥ are formulas there and PK_0 is Resolution (p.15)
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), Theorem 6.7, p.49 (PDF p.51)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_phpCNF
import Definitions.Def_RefWPHP_refCNF
import Definitions.Def_RefWPHP_Supplement_Unsat

namespace RefWPHP

namespace Supplement

/-- Theorem 6.7, p.49 (PDF 51), of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole
Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…): "There exists a sequence of
unsatisfiable CNF formulas `{γ_n}` over `poly(n)` variables and `poly(n)` clauses such that for every
`k, d ∈ ℕ`, if `PK_d` admits polynomial-size refutations of `{PHP^{m²}_m}`, then `PK_{d+O(1)}` admits
polynomial-size refutations of the unsatisfiable formulas `{Ref_{n^k}(γ_n)}`."

**Formalization Note.**
1. `γ_n` has `N n ≤ (n + 2)^a` variables and `M n ≤ (n + 2)^a` clauses for one exponent `a`.
2. The depth increment `O(1)` is one constant `c`, chosen after the family and before `k` and `d`.
3. "Polynomial-size refutations of `{PHP^{m²}_m}`" is: for some exponent `e` and all `m ≥ m₀`, a
   `PK_d`-refutation of size at most `m^e` (`PHP^1_1` is satisfiable, so "for all large `m`");
   likewise in the conclusion, for all `n ≥ n₀`, a `PK_{d+c}`-refutation of `Ref_{n^k}(γ_n)` of size at
   most `n^{e'}`. The size of `PHP^{m²}_m` is polynomial in `m`, and that of `Ref_{n^k}(γ_n)` in `n`.
4. `PK_d` is the base `IsPKRefutation d`, size the base `derivSize`.
5. "the unsatisfiable formulas `{Ref_{n^k}(γ_n)}`" is the unconditional third conjunct: for every
   `k`, for all large `n`, every assignment `v` to the variables of `Ref_{n^k}(γ_n)` falsifies some
   clause (every literal of the clause evaluates to `false`). -/
theorem theorem_6_7 : ∃ (N M : ℕ → ℕ) (γ : (n : ℕ) → Fin (M n) → Finset (Lit (N n))),
    (∀ n, Unsat (γ n)) ∧ (∃ a : ℕ, ∀ n, N n ≤ (n + 2) ^ a ∧ M n ≤ (n + 2) ^ a) ∧
    (∀ k : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ v : RefVar (N n) (M n) (n ^ k) → Bool,
      ∃ Γ ∈ refCNF (γ n) (n ^ k), ∀ ψ ∈ Γ, PKFormula.eval v ψ = false) ∧
    ∃ c : ℕ, ∀ k d : ℕ,
      (∃ e m₀ : ℕ, ∀ m ≥ m₀, ∃ ρ : List (Cedent (Fin (m ^ 2) × Fin m)),
        IsPKRefutation d (phpCNF (m ^ 2) m) ρ ∧ derivSize ρ ≤ m ^ e) →
      ∃ e' n₀ : ℕ, ∀ n ≥ n₀, ∃ ρ : List (Cedent (RefVar (N n) (M n) (n ^ k))),
        IsPKRefutation (d + c) (refCNF (γ n) (n ^ k)) ρ ∧ derivSize ρ ≤ n ^ e' := by sorry

end Supplement

end RefWPHP
