-- Prove2me | Theorems.Thm_StreamSubmod_Supplement_observation_20
-- name    : StreamSubmod.Supplement.observation_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:43:51.532541+00:00
-- url     : https://prove2.me/theorems/4a2ee91c-c7db-40b7-ba8b-439ff673fca7
-- title:
--   Observation 20: all support coordinates of $\hat x$ equal $p$, except at most one when $\|\hat x\|_1=k$
-- statement:
--   Let $V$ be a finite ground set, $f:2^V\to\mathbb R_{\ge0}$ a non-negative submodular function, $k\ge1$, $p\in(0,1)$, $c>0$ and $0\le\tau\le f(\mathrm{OPT})$, where $f(\mathrm{OPT})=\max\{f(S):|S|\le k\}$. Run Algorithm 3 (StreamProcessExtension, simplified) with parameters $(p,c)$ and estimate $\tau$ on a stream presenting every element of $V$ exactly once, in an arbitrary order, and let $\hat x$ be its final fractional solution.
--
--   1. If $\|\hat x\|_1<k$, then $\hat x_e=p$ for every $e\in\operatorname{supp}(\hat x)$.
--   2. Otherwise $\|\hat x\|_1=k$, and there is an element $e_0$ such that $\hat x_e=p$ for every $e\in\operatorname{supp}(\hat x)$ with $e\ne e_0$.
--
--   This structure of $\hat x$ underlies the space bound and the analysis of the case $\|\hat x\|_1<k$.
--
--   Differences from the source:
--   - generalization: Appendix C assumes an estimate τ with (1 − ε/8)·f(OPT) ≤ τ ≤ f(OPT) (p.21) → 0 ≤ τ ≤ f(OPT); reason: the result does not involve ε, and since f ≥ 0 the section's window implies 0 ≤ τ ≤ f(OPT), so the Lean statement covers every τ the paper allows
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E (IsStream), for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k of Algorithm 3 is undefined
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Observation 20, p.23

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_Supplement_Basic
import Definitions.Def_StreamSubmod_Supplement_Algorithm3

namespace StreamSubmod.Supplement

open NonmonotoneSubmod.Shared StreamSubmod in
/-- Observation 20 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.23): if
`‖x̂‖₁ < k`, then `x̂_e = p` for every `e ∈ supp(x̂)`. Otherwise, `‖x̂‖₁ = k`, and the first part
of the observation is still true for every element `e ∈ supp(x̂)` except for maybe a single
element.

**Formalization Note.** `x̂ = alg3Run f k p c τ σ` is the final fractional solution of Algorithm 3
on the stream `σ`. Appendix C assumes `(1 − ε/8) · f(OPT) ≤ τ ≤ f(OPT)` (p.21); this result does
not involve `ε` and is stated under `0 ≤ τ ≤ f(OPT)`, which that assumption implies. -/
theorem observation_20 {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (c : ℝ) (hc : 0 < c)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ optVal f k) (σ : List E) (hσ : IsStream σ) :
    let xh := alg3Run f k p c τ σ
    (l1 xh < (k : ℝ) → ∀ e ∈ supp xh, xh e = p) ∧
    (¬ l1 xh < (k : ℝ) → l1 xh = (k : ℝ) ∧ ∃ e₀ : E, ∀ e ∈ supp xh, e ≠ e₀ → xh e = p) := by sorry

end StreamSubmod.Supplement
