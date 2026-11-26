-- Prove2me | Theorems.Thm_StreamSubmod_Supplement_corollary_26
-- name    : StreamSubmod.Supplement.corollary_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:47:13.405799+00:00
-- url     : https://prove2.me/theorems/6b80757a-722d-5404-a019-4f30ee82f6c5
-- title:
--   Corollary 26: lower bound on $F(\hat x)$ when $\|\hat x\|_1<k$
-- statement:
--   Let $V$ be a finite ground set, $f:2^V\to\mathbb R_{\ge0}$ a non-negative submodular function, $k\ge1$, $p\in(0,1)$, $c>0$ and $0\le\tau\le f(\mathrm{OPT})$, where $f(\mathrm{OPT})=\max\{f(S):|S|\le k\}$. Run Algorithm 3 (StreamProcessExtension, simplified) with parameters $(p,c)$ and estimate $\tau$ on a stream presenting every element of $V$ exactly once, in an arbitrary order, and let $\hat x$ be its final fractional solution. Let $\mathrm{OPT}$ be any set with $|\mathrm{OPT}|\le k$ and $f(\mathrm{OPT})$ maximal, and $b=k^{-1}\cdot|\mathrm{OPT}\setminus\operatorname{supp}(\hat x)|$. If $\|\hat x\|_1<k$, then
--
--   $$
--   F(\hat x)\ \ge\ (1-p)\cdot\bigl[p\cdot f(\mathrm{OPT})+(1-p)\cdot f(\mathrm{OPT}\setminus\operatorname{supp}(\hat x))\bigr]-bc\tau\ \ge\ [p(1-p)-bc]\,\tau+(1-p)^2\cdot f(\mathrm{OPT}\setminus\operatorname{supp}(\hat x)).
--   $$
--
--   Both inequalities are asserted. Since the rounded set $S_1$ has expected value at least $F(\hat x)$, this is one of the two lower bounds combined in Corollary 28.
--
--   Differences from the source:
--   - generalization: Appendix C assumes an estimate τ with (1 − ε/8)·f(OPT) ≤ τ ≤ f(OPT) (p.21) → 0 ≤ τ ≤ f(OPT); reason: the result does not involve ε, and since f ≥ 0 the section's window implies 0 ≤ τ ≤ f(OPT), so the Lean statement covers every τ the paper allows
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E (IsStream), for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k of Algorithm 3 is undefined
--   - encoding: OPT, a fixed optimal solution → every set O with |O| ≤ k and f(O) = f(OPT); reason: the paper's OPT is an arbitrary optimal solution; the statement holds for each of them
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Corollary 26, p.25

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_Supplement_Basic
import Definitions.Def_StreamSubmod_Supplement_Algorithm3

namespace StreamSubmod.Supplement

open NonmonotoneSubmod.Shared StreamSubmod in
/-- Corollary 26 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.25): if `‖x̂‖₁ < k`,
then `F(x̂) ≥ (1 − p) · [p · f(OPT) + (1 − p) · f(OPT ∖ supp(x̂))] − bcτ
≥ [p(1 − p) − bc]τ + (1 − p)² · f(OPT ∖ supp(x̂))`, with `b = k⁻¹ · |OPT ∖ supp(x̂)|`.

**Formalization Note.** `x̂ = alg3Run f k p c τ σ` is the final fractional solution of Algorithm 3
on the stream `σ`. Appendix C assumes `(1 − ε/8) · f(OPT) ≤ τ ≤ f(OPT)` (p.21); this result does
not involve `ε` and is stated under `0 ≤ τ ≤ f(OPT)`, which that assumption implies. `OPT` is any set `O` with `|O| ≤ k` and `f(O) = f(OPT)`. -/
theorem corollary_26 {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (c : ℝ) (hc : 0 < c)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ optVal f k) (σ : List E) (hσ : IsStream σ)
    (O : Finset E) (hOk : O.card ≤ k) (hOopt : f O = optVal f k) :
    let xh := alg3Run f k p c τ σ
    let b : ℝ := ((O \ supp xh).card : ℝ) / (k : ℝ)
    l1 xh < (k : ℝ) →
      (1 - p) * (p * f O + (1 - p) * f (O \ supp xh)) - b * c * τ ≤ F f xh ∧
      (p * (1 - p) - b * c) * τ + (1 - p) ^ 2 * f (O \ supp xh) ≤
        (1 - p) * (p * f O + (1 - p) * f (O \ supp xh)) - b * c * τ := by sorry

end StreamSubmod.Supplement
