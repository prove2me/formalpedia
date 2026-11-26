-- Prove2me | Theorems.Thm_StreamSubmod_Supplement_lemma_24
-- name    : StreamSubmod.Supplement.lemma_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:46:07.567535+00:00
-- url     : https://prove2.me/theorems/1c72310e-e0fb-5e52-ac41-e026763fded7
-- title:
--   Lemma 24: lower bound on $F(\hat x+\mathbf 1_{\mathrm{OPT}\setminus\operatorname{supp}(\hat x)})$
-- statement:
--   Let $V$ be a finite ground set, $f:2^V\to\mathbb R_{\ge0}$ a non-negative submodular function, $k\ge1$, $p\in(0,1)$, $c>0$ and $0\le\tau\le f(\mathrm{OPT})$, where $f(\mathrm{OPT})=\max\{f(S):|S|\le k\}$. Run Algorithm 3 (StreamProcessExtension, simplified) with parameters $(p,c)$ and estimate $\tau$ on a stream presenting every element of $V$ exactly once, in an arbitrary order, and let $\hat x$ be its final fractional solution. Let $\mathrm{OPT}$ be any set with $|\mathrm{OPT}|\le k$ and $f(\mathrm{OPT})$ maximal,. If $\|\hat x\|_1<k$, then
--
--   $$
--   F\bigl(\hat x+\mathbf 1_{\mathrm{OPT}\setminus\operatorname{supp}(\hat x)}\bigr)\ \ge\ (1-p)\cdot\bigl[p\cdot f(\mathrm{OPT})+(1-p)\cdot f(\mathrm{OPT}\setminus\operatorname{supp}(\hat x))\bigr].
--   $$
--
--   Together with Lemma 25 this gives the lower bound on $F(\hat x)$ of Corollary 26.
--
--   Differences from the source:
--   - generalization: Appendix C assumes an estimate τ with (1 − ε/8)·f(OPT) ≤ τ ≤ f(OPT) (p.21) → 0 ≤ τ ≤ f(OPT); reason: the result does not involve ε, and since f ≥ 0 the section's window implies 0 ≤ τ ≤ f(OPT), so the Lean statement covers every τ the paper allows
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E (IsStream), for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k of Algorithm 3 is undefined
--   - encoding: OPT, a fixed optimal solution → every set O with |O| ≤ k and f(O) = f(OPT); reason: the paper's OPT is an arbitrary optimal solution; the statement holds for each of them
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Lemma 24, p.24

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_Supplement_Basic
import Definitions.Def_StreamSubmod_Supplement_Algorithm3

namespace StreamSubmod.Supplement

open NonmonotoneSubmod.Shared StreamSubmod in
/-- Lemma 24 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.24): if `‖x̂‖₁ < k`, then
`F(x̂ + 𝟏_{OPT∖supp(x̂)}) ≥ (1 − p) · [p · f(OPT) + (1 − p) · f(OPT ∖ supp(x̂))]`.

**Formalization Note.** `x̂ = alg3Run f k p c τ σ` is the final fractional solution of Algorithm 3
on the stream `σ`. Appendix C assumes `(1 − ε/8) · f(OPT) ≤ τ ≤ f(OPT)` (p.21); this result does
not involve `ε` and is stated under `0 ≤ τ ≤ f(OPT)`, which that assumption implies. `OPT` is any set `O` with `|O| ≤ k` and `f(O) = f(OPT)`. -/
theorem lemma_24 {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (c : ℝ) (hc : 0 < c)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ optVal f k) (σ : List E) (hσ : IsStream σ)
    (O : Finset E) (hOk : O.card ≤ k) (hOopt : f O = optVal f k) :
    let xh := alg3Run f k p c τ σ
    l1 xh < (k : ℝ) →
      (1 - p) * (p * f O + (1 - p) * f (O \ supp xh)) ≤
        F f (fun e => xh e + ind (O \ supp xh) e) := by sorry

end StreamSubmod.Supplement
