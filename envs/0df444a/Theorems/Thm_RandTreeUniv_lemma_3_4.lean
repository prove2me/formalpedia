-- Prove2me | Theorems.Thm_RandTreeUniv_lemma_3_4
-- name    : RandTreeUniv.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:15.479077+00:00
-- url     : https://prove2.me/theorems/b97ac475-ed7f-46ef-8dd9-5b194f646fb9
-- title:
--   Lemma 3.4 — optimal-depth linking systems in $G(\delta n,p(n))$
-- statement:
--   Fix $\delta\in(0,1]$ and let $p=p(n)=\frac{2C_0}{\delta}\cdot\frac{(\ln n)^{\psi(n)}}{n}$ with $C_0=10^5$ and $\psi(n)\in[1,\ln n/(4\ln\ln n)]$. Consider integers $k\ge4e\,k^*(n,\psi)$ and $m=\delta n/(2k+1)$, and disjoint $m$-tuples $\mathbf a,\mathbf b\subseteq[\delta n]$ of distinct vertices. Then whp
--
--   $$
--   G(\delta n,p)\ \text{contains an}\ (\mathbf a,\mathbf b;2k)\text{-linking system}.
--   $$
--
--   The probability and the depth are computed from $n$, not from $\delta n$; this is what allows the lemma to be applied inside a vertex set of size proportional to $n$ (as in the proof of Theorem 5.1) without controlling $\psi(\delta n)/\psi(n)$.
--
--   Differences from the source:
--   - reading: G(δn, p) and [δn] → G(⌊δn⌋, p(n)) on Fin ⌊δn⌋, with m an integer as (2k + 1) ∣ ⌊δn⌋; reason: the paper ignores rounding (§2.1); ⌊δn⌋ is the number of vertices
--   - reading: whp / o(·) for fixed functions ψ(n), k(n) and fixed tuples → uniform over all admissible ψ, k and tuples at each n (for every ε > 0 there is N such that …); reason: equivalent: a non-uniform failure yields a choice of functions and tuples along which the paper's statement fails
--   - encoding: G(n,p) with p = p(n) a probability → published erProb n p, which clamps p to [0,1]; reason: the clamp is the identity on [0,1], and the edge probabilities used lie in [0,1] for all large n
--   - encoding: disjoint m-tuples with different elements → injective maps with disjoint ranges; reason: same tuples
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Lemma 3.4, pp.14–15 (PDF 15–16); proof in Appendix A, p.57 (PDF 58)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_RandTreeUniv_IsLinkingSystemIn
import Definitions.Def_RandTreeUniv_kStar

set_option autoImplicit false

open scoped Classical
open LPCommunity.SBMRecovery

namespace RandTreeUniv

/-- **Lemma 3.4** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), pp.14–15 (PDF 15–16); restated and proved in Appendix A, p.57). Fix
`δ ∈ (0, 1]`, set `p = p(n) := (2C₀/δ)·(ln n)^{ψ(n)}/n`, and consider integers `k ≥ 4e k∗(n, ψ)` and
`m = δn/(2k + 1)`. Fix disjoint `m`-tuples with different elements `a, b ⊆ [δn]`. Then, whp
`G(δn, p)` contains an `(a, b; 2k)`-linking system.

**Formalization Note** `δn` is read as `⌊δn⌋`: the graph is `G(⌊δn⌋, p(n))` on `Fin ⌊δn⌋`, with
`p` and `k∗` computed at `n`. `m` being an integer is `2k + 1 ∣ ⌊δn⌋`. whp is stated uniformly over the
parameters at each `n`: for every `ε > 0` there is `N` such that for all `n ≥ N`, all
`ψ ∈ [1, ln n/(4 ln ln n)]`, all integers `k ≥ 4e·k∗(n, ψ)` with `2k + 1 ∣ ⌊δn⌋` and all injective
tuples with disjoint ranges, the probability is at least `1 − ε` (`δ` is fixed first). `e` is
`Real.exp 1`; `C₀ = 10⁵`. -/
theorem lemma_3_4 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ ψ : ℝ, 1 ≤ ψ → ψ ≤ Real.log n / (4 * Real.log (Real.log n)) →
      ∀ k : ℕ, 4 * Real.exp 1 * (kStar n ψ : ℝ) ≤ k → (2 * k + 1) ∣ ⌊δ * n⌋₊ →
      ∀ a b : Fin (⌊δ * n⌋₊ / (2 * k + 1)) → Fin ⌊δ * n⌋₊,
        Function.Injective a → Function.Injective b → (∀ i j, a i ≠ b j) →
        1 - ε ≤ erProb ⌊δ * n⌋₊ (2 * C0 / δ * Real.log n ^ ψ / n)
          (fun G => IsLinkingSystemIn G Set.univ a b (2 * k)) := by sorry

end RandTreeUniv
