-- Prove2me | Theorems.Thm_RefWPHP_Supplement_theorem_4_4
-- name    : RefWPHP.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:26:49.535376+00:00
-- url     : https://prove2.me/theorems/821abcf6-3a25-404e-8f22-ddc213f1dbc2
-- title:
--   Theorem 4.4 — under the WPHP Hypothesis, every PK$_d$ refutation of $\mathrm{Ref}_s(\varphi)$, $s = \lfloor 2^{\varepsilon n}\rfloor$, has size $> s^k$
-- statement:
--   Assume the WPHP Hypothesis (Hypothesis 1.4). Then for every $d \in \mathbb N$, every real $0 < \varepsilon \le 1$ and every $k \in \mathbb N$ there is $n_0 \in \mathbb N$ with the following property. For every unsatisfiable CNF formula $\varphi$ over $n \ge n_0$ variables with $m \le 3^n$ clauses, and for
--
--   $$
--   s = \lfloor 2^{\varepsilon n} \rfloor,
--   $$
--
--   every $\mathrm{PK}_d$-refutation of $\mathrm{Ref}_s(\varphi)$ has size strictly larger than $s^k$.
--
--   So, under the hypothesis, constant-depth Frege cannot prove exponential Resolution lower bounds $2^{\varepsilon n}$ for any unsatisfiable formula in polynomial size. This is the form used in Theorem 5.1.
--
--   **Formalization Note** The hypothesis is the argument `hW : WPHPHypothesis`. $\mathrm{PK}_d$ refutations are the base `IsPKRefutation d`, $\mathrm{Ref}_s(\varphi)$ the base `refCNF φ s`, and $s$ is the natural-number floor of the real $2^{\varepsilon n}$. The threshold $n_0$ depends on $d$, $\varepsilon$ and $k$ only.
--
--   Differences from the source:
--   - encoding: Assume the WPHP Hypothesis (Hypothesis 1.4), with f_d = ω(1) → hypothesis hW : WPHPHypothesis, with f : ℕ → ℝ, f n → ∞; reason: "Assume" is an implication; ω(1) is divergence to +∞
--   - encoding: an unsatisfiable CNF over n variables and m clauses → φ : Fin m → Finset (Lit n) with Unsat φ; n counts every variable, m counts clauses with repetition; reason: the base mission's representation of CNFs; no instance changes
--   - encoding: size is the length of a binary string (p.15); "in size T" → derivSize, the symbol count plus one per line; size at most T; reason: the two sizes differ by at most a logarithmic factor in the number of variables, which every bound in the statement absorbs (base mission convention)
--   - encoding: the variables a-lit^A_ℓ of Ref_s(φ) → constants 1{ℓ ∈ C_A}: (Ref-3) only for ℓ ∈ C_A, without that literal; reason: p.22 fixes them as constants for a fixed φ; the omitted instances are satisfied (base mission's refCNF)
--   - encoding: CNF clauses (of φ, Ref_s(φ), PHP, ontoPHP) written with → and ⋁ → each clause is the cedent of its literals; reason: p.15 collects a CNF into a set of cedents; no instance changes (base mission convention)
--   - reading: binary ∧/∨-Intro used as "repeated ∧-introduction", Cut on φ₁ ∧ ⋯ ∧ φ_m, cedents as sequences → the base PKStep: n-ary ∧/∨-introduction, Atomic LEM, weakening to any list containing the premise, Cut on one formula and on a conjunction, hypotheses; dag-like lines; reason: the base mission's published calculus; ⊤ and ⊥ are formulas there and PK_0 is Resolution (p.15)
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), Theorem 4.4, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_refCNF
import Definitions.Def_RefWPHP_Supplement_Unsat
import Definitions.Def_RefWPHP_Supplement_WPHPHypothesis

namespace RefWPHP

namespace Supplement

/-- Theorem 4.4, p.35 (PDF 37), of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole
Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…): "Assume the WPHP Hypothesis
(Hypothesis 1.4). For every `d ∈ ℕ`, every `0 < ε ≤ 1` and every `k ∈ ℕ`, there exists `n₀ ∈ ℕ` such
that for every unsatisfiable CNF formula `φ` over `n ≥ n₀` variables and `m ≤ 3^n` clauses, every
`PK_d`-refutation of `Ref_s(φ)` for `s = ⌊2^{εn}⌋` has size strictly larger than `s^k`."

**Formalization Note.** The WPHP Hypothesis is the hypothesis `hW`, not an axiom. `PK_d` is the
base `IsPKRefutation d`, size the base `derivSize`, and `s = ⌊2^{εn}⌋₊` (floor of a real). `n₀`
depends on `d`, `ε`, `k` only. -/
theorem theorem_4_4 (hW : WPHPHypothesis) : ∀ (d : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ k : ℕ,
    ∃ n₀ : ℕ, ∀ {n m : ℕ} (φ : Fin m → Finset (Lit n)), n₀ ≤ n → m ≤ 3 ^ n → Unsat φ →
      ∀ ρ : List (Cedent (RefVar n m ⌊(2 : ℝ) ^ (ε * n)⌋₊)),
        IsPKRefutation d (refCNF φ ⌊(2 : ℝ) ^ (ε * n)⌋₊) ρ →
          ⌊(2 : ℝ) ^ (ε * n)⌋₊ ^ k < derivSize ρ := by sorry

end Supplement

end RefWPHP
