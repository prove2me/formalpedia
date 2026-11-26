-- Prove2me | Theorems.Thm_StreamSubmod_Supplement_lemma_27
-- name    : StreamSubmod.Supplement.lemma_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:47:54.216257+00:00
-- url     : https://prove2.me/theorems/161e6d89-6ad9-45c6-90fe-a02af92dec0b
-- title:
--   Lemma 27: lower bound on $\mathbb E[f(S_2)]$ when $\|\hat x\|_1<k$
-- statement:
--   Let $V$ be a finite ground set, $f:2^V\to\mathbb R_{\ge0}$ a non-negative submodular function, $k\ge1$, $p\in(0,1)$, $c>0$ and $0\le\tau\le f(\mathrm{OPT})$, where $f(\mathrm{OPT})=\max\{f(S):|S|\le k\}$. Run Algorithm 3 (StreamProcessExtension, simplified) with parameters $(p,c)$ and estimate $\tau$ on a stream presenting every element of $V$ exactly once, in an arbitrary order, and let $\hat x$ be its final fractional solution. Let $\mathrm{OPT}$ be any set with $|\mathrm{OPT}|\le k$ and $f(\mathrm{OPT})$ maximal, and $b=k^{-1}\cdot|\mathrm{OPT}\setminus\operatorname{supp}(\hat x)|$. Let OfflineAlg be an $\alpha$-approximation offline algorithm, $0<\alpha\le1$, and let $S_2$ be its output with $\operatorname{supp}(\hat x)$ as the ground set (line 5 of Algorithm 3). If $\|\hat x\|_1<k$, then
--
--   $$
--   \mathbb E[f(S_2)]\ \ge\ \alpha b(1-p-cb)\,\tau+\alpha(1-b)\cdot f(\mathrm{OPT}\cap\operatorname{supp}(\hat x)).
--   $$
--
--   This is the second lower bound combined in Corollary 28.
--
--   **Formalization Note** The randomness of OfflineAlg is a finite seed type with a probability vector $\mu$, and $\mathbb E[f(S_2)]=\sum_\omega\mu(\omega)f(S_2(\omega))$.
--
--   Differences from the source:
--   - generalization: Appendix C assumes an estimate τ with (1 − ε/8)·f(OPT) ≤ τ ≤ f(OPT) (p.21) → 0 ≤ τ ≤ f(OPT); reason: the result does not involve ε, and since f ≥ 0 the section's window implies 0 ≤ τ ≤ f(OPT), so the Lean statement covers every τ the paper allows
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E (IsStream), for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k of Algorithm 3 is undefined
--   - encoding: OPT, a fixed optimal solution → every set O with |O| ≤ k and f(O) = f(OPT); reason: the paper's OPT is an arbitrary optimal solution; the statement holds for each of them
--   - encoding: a possibly randomized OfflineAlg → a finite seed type Ω with a probability vector μ; Off ω U is the output on U with seed ω; reason: outputs are subsets of a finite set, so every randomized algorithm has this form
--   - generalization: OfflineAlg is an α-approximation algorithm for every instance of the problem → IsApproxOffline f k α μ Off: the guarantee is assumed only for the given f and k, on every ground set U ⊆ V; reason: Algorithm 3 calls OfflineAlg only with this f and k, so an algorithm that is α-approximate on every instance satisfies the hypothesis
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Lemma 27, p.25

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Supplement_Basic
import Definitions.Def_StreamSubmod_Supplement_Algorithm3

namespace StreamSubmod.Supplement

open NonmonotoneSubmod.Shared StreamSubmod in
/-- Lemma 27 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.25): if `‖x̂‖₁ < k`, then
`E[f(S₂)] ≥ αb(1 − p − cb)τ + α(1 − b) · f(OPT ∩ supp(x̂))`, where `S₂` is the output of
OfflineAlg with `supp(x̂)` as the ground set (Algorithm 3, line 5) and `b = k⁻¹ · |OPT ∖ supp(x̂)|`.

**Formalization Note.** `x̂ = alg3Run f k p c τ σ` is the final fractional solution of Algorithm 3
on the stream `σ`. Appendix C assumes `(1 − ε/8) · f(OPT) ≤ τ ≤ f(OPT)` (p.21); this result does
not involve `ε` and is stated under `0 ≤ τ ≤ f(OPT)`, which that assumption implies. `OPT` is any set `O` with `|O| ≤ k` and `f(O) = f(OPT)`. OfflineAlg is an `α`-approximation with seeds `ω` of probability `μ ω`
(`IsApproxOffline`), and `E[f(S₂)] = Σ_ω μ(ω) f(Off ω (supp x̂))`. -/
theorem lemma_27 {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (c : ℝ) (hc : 0 < c)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (Off : Ω → Finset E → Finset E) (hOff : IsApproxOffline f k α μ Off)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ optVal f k) (σ : List E) (hσ : IsStream σ)
    (O : Finset E) (hOk : O.card ≤ k) (hOopt : f O = optVal f k) :
    let xh := alg3Run f k p c τ σ
    let b : ℝ := ((O \ supp xh).card : ℝ) / (k : ℝ)
    l1 xh < (k : ℝ) →
      α * b * (1 - p - c * b) * τ + α * (1 - b) * f (O ∩ supp xh) ≤
        ∑ ω, μ ω * f (Off ω (supp xh)) := by sorry

end StreamSubmod.Supplement
