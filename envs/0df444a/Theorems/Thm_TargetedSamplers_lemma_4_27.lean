-- Prove2me | Theorems.Thm_TargetedSamplers_lemma_4_27
-- name    : TargetedSamplers.lemma_4_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:05:36.299497+00:00
-- url     : https://prove2.me/theorems/195c0624-6d6e-4999-8b70-648cd0508896
-- title:
--   Lemma 4.27 — almost pairwise independent hashing
-- statement:
--   There are one deterministic program and universal constants such that for every $n,m\in\mathbb N$ and $0<\epsilon<1$ there is a family $\{h_k:\{0,1\}^n\to\{0,1\}^m\}_{k\in\{0,1\}^\kappa}$ with $\kappa\le K(m+\log_2n+\log_2(1/\epsilon)+1)$ and
--   $$\Pr_{k}[h_k(x_1)=y_1\wedge h_k(x_2)=y_2]\le\frac{1+\epsilon}{2^{2m}}$$
--   for all distinct $x_1,x_2\in\{0,1\}^n$ and all $y_1,y_2\in\{0,1\}^m$. Given $k$ and $x$, the program outputs $h_k(x)$ in time $\tilde O(|k|+|x|)$. A key is sampled with $\kappa$ random bits.
--
--   The reconstruction of Proposition 4.26 hashes blocks with such a family.
--
--   Differences from the source:
--   - reading: "there exists a deterministic algorithm", after "for every n, m, ϵ" → one program and one constant for all n, m, ϵ; reason: a separate program per (n, m, ϵ) could be a table lookup, which makes the time bound empty
--   - encoding: K = {0,1}^{O(m + log n + log(1/ϵ))} → κ ≤ K·(m + log₂ n + log₂(1/ϵ) + 1); reason: O(·) of a quantity that can be near 0
--   - encoding: input (k, x) → encInput [] [k, x]; reason: the page fixes no encoding
--   - reading: "runs in time t" on an unspecified RAM → time at most budget = K·(t+1)·(log₂(n+t+2)+1)^k on the log-cost RAM; reason: the paper fixes no cost model; the log-cost RAM differs from a word RAM by polylogarithmic factors
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Lemma 4.27, p.37 (pdf p.39)

import Mathlib
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_TargetedSamplers_encInput

namespace TargetedSamplers

/-- Lemma 4.27 (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission, manuscript
sha256 599d0a59…, p.37). For every `n, m ∈ ℕ` and `0 < ϵ < 1` there is an `ϵ`-almost pairwise
independent hash family `H = {h_k : {0,1}ⁿ → {0,1}^m}_{k ∈ K}` with key space
`K = {0,1}^{O(m + log n + log(1/ϵ))}` satisfying
`Pr_{k←K}[h_k(x₁) = y₁ ∧ h_k(x₂) = y₂] ≤ (1 + ϵ)/2^{2m}` for all distinct `x₁, x₂ ∈ {0,1}ⁿ` and all
`y₁, y₂ ∈ {0,1}^m`; a key is sampled with `O(m + log n + log(1/ϵ))` random bits, and one deterministic
algorithm, given `k ∈ K` and `x ∈ {0,1}ⁿ`, outputs `h_k(x)` in time `Õ(|k| + |x|)`.

**Formalization Note** The constant of `O(·)` and the algorithm are chosen before `n, m, ϵ` (one
algorithm for all families; a per-family algorithm could be a table lookup). The algorithm gets only
`k` and `x`. Keys are uniform on `{0,1}^κ`, so sampling a key takes `κ` random bits. The `+ 1` keeps
the `O(·)` bound meaningful when `m + log n + log(1/ϵ)` is near 0. Time is `budget`. -/
theorem lemma_4_27 : ∃ (P : Program) (K : ℝ) (K' k : ℕ), 0 < K ∧
    ∀ (n m : ℕ) (ϵ : ℝ), 0 < ϵ → ϵ < 1 →
    ∃ (κ : ℕ) (h : (Fin κ → Bool) → (Fin n → Bool) → (Fin m → Bool)),
      (κ : ℝ) ≤ K * (m + Real.logb 2 n + Real.logb 2 (1 / ϵ) + 1) ∧
      (∀ x₁ x₂ : Fin n → Bool, x₁ ≠ x₂ → ∀ y₁ y₂ : Fin m → Bool,
        ((Finset.univ.filter (fun key => h key x₁ = y₁ ∧ h key x₂ = y₂)).card : ℝ) / 2 ^ κ ≤
          (1 + ϵ) / 2 ^ (2 * m)) ∧
      ∀ (key : Fin κ → Bool) (x : Fin n → Bool),
        P.RunsIn (Tapes.ofInput (encInput [] [List.ofFn key, List.ofFn x]))
          (budget K' k (κ + n) (κ + n)) (some (List.ofFn (h key x))) := by sorry

end TargetedSamplers
