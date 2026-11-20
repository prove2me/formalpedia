-- Prove2me | Theorems.Thm_UniversalSubmod_Supplement_theorem_1_2
-- name    : UniversalSubmod.Supplement.theorem_1_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-15T17:41:12.437211+00:00
-- url     : https://prove2.me/theorems/f5cf53e2-8244-4071-a971-a49b2dacfa59
-- title:
--   Theorem 1.2 — a distribution with $n^{O(\varepsilon^{-4}\log(1/\varepsilon))}$ support estimates the uniform expectation of every nonnegative submodular function within $1-\varepsilon$
-- statement:
--   Let $n\ge 2$ and let $f:2^{[n]}\to\mathbb R$ be **nonnegative** ($f(S)\ge 0$ for all $S\subseteq[n]$) and **submodular** ($f(S\cup T)+f(S\cap T)\le f(S)+f(T)$ for all $S,T$). Write $\mathcal U_n$ for the uniform distribution on the $2^n$ subsets of $[n]$, so that
--   $$
--   \mathbb E_{R\sim\mathcal U_n}[f(R)]=\frac1{2^n}\sum_{S\subseteq[n]}f(S).
--   $$
--   There is an absolute constant $C$ such that for every $\varepsilon\in(0,1)$ and every $n\ge 2$ there is a probability distribution $\mathcal D_{n,\varepsilon}$ on subsets of $[n]$ whose support has at most
--   $$
--   n^{\,C\,\varepsilon^{-4}\,(1+\log(1/\varepsilon))}
--   $$
--   sets, and which satisfies, simultaneously for every nonnegative submodular $f:2^{[n]}\to\mathbb R$,
--   $$
--   \mathbb E_{R\sim\mathcal U_n}[f(R)]\;\ge\;\mathbb E_{R\sim\mathcal D_{n,\varepsilon}}[f(R)]\;\ge\;(1-\varepsilon)\,\mathbb E_{R\sim\mathcal U_n}[f(R)].
--   $$
--   The distribution is fixed before $f$ is chosen.
--
--   So the uniform expectation of every nonnegative submodular function can be estimated within a factor $1-\varepsilon$, from below, by averaging over polynomially many sets (for fixed $\varepsilon$). The paper's Theorem 1.3 shows that polynomially many independent uniform samples cannot do this, which is why the distribution has to be constructed.
--
--   **Formalization Note** The ground set $[n]$ is `Fin n` and subsets are `Finset (Fin n)`. The distribution is a weight function $w$ with $w\ge0$ and $\sum_S w(S)=1$; its expectation is $\sum_S w(S)f(S)$ and its support is $\{S : w(S)>0\}$. Submodularity is the published `NonmonotoneSubmod.Shared.Submodular`. The power is a real power.
--
--   Differences from the source:
--   - encoding: support of size $n^{O(1/\varepsilon^4\log(1/\varepsilon))}$ → one absolute $C$ chosen before $\varepsilon$ and $n$, with support at most $n^{C\varepsilon^{-4}(1+\log(1/\varepsilon))}$; reason: the $O(\cdot)$ is read as $\varepsilon\to0$, where $1+\log(1/\varepsilon)\le 2\log(1/\varepsilon)$, so this is the same strength, and it is what the proof gives (p.15, after reducing to $\varepsilon<1/4$). The literal exponent $C\varepsilon^{-4}\log(1/\varepsilon)$ tends to $0$ as $\varepsilon\to1$, which would force a support of one set $S$; no point mass satisfies both inequalities ($S\ne\emptyset$: $f(T)=|T\cap S|$ gives $f(S)=|S|>|S|/2=\mathbb E_{\mathcal U_n}f$; $S=\emptyset$: $f(T)=|T|$ gives $0<(1-\varepsilon)n/2$), so that reading is false for every $C$.
--   - encoding: a distribution $\mathcal D_{n,\varepsilon}$ over subsets of $[n]$ → nonnegative weights $w$ on `Finset (Fin n)` summing to $1$, support $\{S: w(S)>0\}$; reason: a distribution on a finite set is its probability mass function.
--   - encoding: the ground set $[n]$, $f:2^{[n]}\to\mathbb R$ nonnegative → `Fin n`, `Finset (Fin n)`, real-valued $f$ with $f(S)\ge0$ for all $S$; reason: a relabelling of $[n]$; the same functions.
-- source:
--   Adamczyk, Ueltzen, Vondrák, Optimal universal sets for submodular functions, manuscript (Nov. 3, 2026; sha256 8a53c0912e8ad39b1019cbabfbde98980fd3eea456a8c7e5b28eb55d58343714), Theorem 1.2, p.3 (proof §4.4, pp.15–16)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace UniversalSubmod.Supplement

open NonmonotoneSubmod.Shared

/-- **Theorem 1.2** (a distribution of polynomial support estimating the uniform expectation;
Adamczyk, Ueltzen, Vondrák, *Optimal universal sets for submodular functions*, manuscript of
November 3, 2026, Theorem 1.2, p.3; proof §4.4, pp.15–16). For every `ε ∈ (0, 1)` and `n ≥ 2`,
there is a distribution `D_{n,ε}` over subsets of `[n]`, with support of size
`n^{O(1/ε⁴ log(1/ε))}`, such that for every nonnegative submodular function `f : 2^[n] → ℝ`,
`E_{R∼U_n}[f(R)] ≥ E_{R∼D_{n,ε}}[f(R)] ≥ (1 − ε) E_{R∼U_n}[f(R)]`, where `U_n` is the uniform
distribution over subsets of `[n]`.

**Formalization Note.** `[n]` is `Fin n` and subsets are `Finset (Fin n)`; `f` is real valued with
`f ≥ 0` and the published `Submodular` (no normalization, no monotonicity). The distribution
`D_{n,ε}` is a weight function `w` with `w ≥ 0` and `∑_S w(S) = 1`; `E_{R∼D}[f(R)] = ∑_S w(S) f(S)`;
its support is the set of `S` with `w(S) > 0`. `E_{R∼U_n}[f(R)] = 2^{-n} ∑_S f(S)`. The
distribution is chosen before `f`. The `O(·)` is read as `ε → 0` with one absolute constant `C`
chosen before `ε` and `n`: `|supp D| ≤ n^{C ε⁻⁴ (1 + log(1/ε))}` (real power). The literal
exponent `C ε⁻⁴ log(1/ε)` tends to `0` as `ε → 1`, which would force a point mass, and no point
mass satisfies both inequalities (modular `f(T) = |T ∩ S|` or `f(T) = |T|`). -/
theorem theorem_1_2 :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ n : ℕ, 2 ≤ n →
      ∃ w : Finset (Fin n) → ℝ,
        (∀ S, 0 ≤ w S) ∧ (∑ S, w S) = 1 ∧
        ((Finset.univ.filter (fun S => 0 < w S)).card : ℝ) ≤
          (n : ℝ) ^ (C * (1 / ε ^ 4) * (1 + Real.log (1 / ε))) ∧
        ∀ f : Finset (Fin n) → ℝ, (∀ S, 0 ≤ f S) → Submodular f →
          (∑ S, w S * f S) ≤ (∑ S, f S) / 2 ^ n ∧
          (1 - ε) * ((∑ S, f S) / 2 ^ n) ≤ ∑ S, w S * f S := by sorry

end UniversalSubmod.Supplement
