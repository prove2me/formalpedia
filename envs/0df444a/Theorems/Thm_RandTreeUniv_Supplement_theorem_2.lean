-- Prove2me | Theorems.Thm_RandTreeUniv_Supplement_theorem_2
-- name    : RandTreeUniv.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:38:22.879201+00:00
-- url     : https://prove2.me/theorems/65744dfd-d58a-4449-a274-af1fae35d6dc
-- title:
--   Theorem 2 — whp $G(n, C(\ln n)^\psi/n)$ contains an $(\mathbf a,\mathbf b;k)$-linking system for every depth $k\ge 50\ln n/(\psi\ln\ln n)$
-- statement:
--   Let $\psi=\psi(n)\in\bigl[1,\ \frac{\ln n}{4\ln\ln n}\bigr]$ and let $k$ be an integer with
--
--   $$
--   k\ \ge\ \frac{50\ln n}{\psi\ln\ln n}\qquad\text{and}\qquad m=\frac{n}{k+1}\in\mathbb N .
--   $$
--
--   Fix two disjoint $m$-tuples $\mathbf a=(a_1,\dots,a_m)$ and $\mathbf b=(b_1,\dots,b_m)$ of distinct vertices of $[n]$. An **$(\mathbf a,\mathbf b;k)$-linking system** in a graph $G$ is the requirement that for every permutation $\sigma$ of $[m]$ there are $m$ vertex-disjoint paths in $G$, each of length exactly $k$, the $i$-th joining $a_i$ to $b_{\sigma(i)}$ (since $(k+1)m=n$, such paths cover all vertices).
--
--   **Theorem.** There is an absolute constant $C_0$ such that for every $C\ge C_0$: with high probability (probability tending to $1$ as $n\to\infty$) the binomial random graph $G\sim G(n,C(\ln n)^\psi/n)$ contains an $(\mathbf a,\mathbf b;k)$-linking system.
--
--   The depth is optimal up to a constant factor: by a union bound, $G(n,C(\ln n)^\psi/n)$ whp contains no such family of paths of length $\ln n/((1+\varepsilon)\psi\ln\ln n)$. The case $\psi=1$ (Corollary 3) is a key ingredient of the proof of Theorem 1, and the result is the source of the paper's general universality theorem (Theorem 5.1).
--
--   **Formalization Note** $G(n,p)$ is the published law `erProb n p` on graphs on `Fin n`. The tuples are injective maps $\mathrm{Fin}(n/(k+1))\to\mathrm{Fin}\,n$ with disjoint ranges, and the linking system is the published `IsLinkingSystemIn G Set.univ a b k`. "With high probability" is stated uniformly in the parameters: for every $\varepsilon>0$ there is $N$ such that for all $n\ge N$, every admissible $\psi$, $k$ and tuples, the probability is at least $1-\varepsilon$.
--
--   Differences from the source:
--   - reading: "Let C be a large enough absolute constant" → ∃ C₀, ∀ C ≥ C₀, chosen before ψ, k, the tuples and n; reason: the standard meaning of "large enough"
--   - reading: whp for fixed functions ψ(n), k(n) and fixed tuples → uniform over all admissible ψ, k and tuples at each n (for every ε > 0 there is N such that …); reason: equivalent: a non-uniform failure yields a choice of functions and tuples along which the paper's statement fails
--   - encoding: G(n,p) with p = p(n) a probability → published erProb n p, which clamps p to [0,1]; reason: the clamp is the identity on [0,1], and C(ln n)^ψ/n ≤ C n^{1/4}/n lies in [0,1] for all large n
--   - encoding: disjoint m-tuples of different vertices, m = n/(k+1) ∈ ℕ → injective maps Fin (n/(k+1)) → Fin n with disjoint ranges, under (k + 1) ∣ n; reason: same tuples
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Theorem 2, p.5 (PDF 6); Definition 1.1, pp.3–4 (PDF 4–5)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_RandTreeUniv_IsLinkingSystemIn

set_option autoImplicit false

open scoped Classical
open LPCommunity.SBMRecovery

namespace RandTreeUniv.Supplement

/-- **Theorem 2** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal
linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.5
(PDF 6)). Let `C` be a large enough absolute constant. Consider `ψ = ψ(n) ∈ [1, ln n/(4 ln ln n)]`
and an integer `k ≥ 50 ln n/(ψ ln ln n)` such that `m = n/(k + 1) ∈ ℕ`. Fix disjoint `m`-tuples of
different vertices `a, b ∈ [n]^m`. Then, whp `G ∼ G(n, C(ln n)^ψ/n)` contains an
`(a, b; k)`-linking system.

**Formalization Note** "`C` large enough" is: there is `C₀` such that every `C ≥ C₀` works.
`G(n, p)` is the published law `erProb n p` on graphs on `Fin n` (`p` clamped to `[0, 1]`).
`m ∈ ℕ` is `k + 1 ∣ n`, and the tuples are injective maps `Fin (n/(k+1)) → Fin n` with disjoint
ranges. whp is stated uniformly over the parameters at each `n`: for every `ε > 0` there is `N`
such that for all `n ≥ N`, all `ψ` in the range, all admissible `k` and all such tuples, the
probability is at least `1 − ε`. The linking system is `IsLinkingSystemIn G Set.univ a b k`. -/
theorem theorem_2 :
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ ψ : ℝ, 1 ≤ ψ → ψ ≤ Real.log n / (4 * Real.log (Real.log n)) →
        ∀ k : ℕ, 50 * Real.log n / (ψ * Real.log (Real.log n)) ≤ k → (k + 1) ∣ n →
        ∀ a b : Fin (n / (k + 1)) → Fin n,
          Function.Injective a → Function.Injective b → (∀ i j, a i ≠ b j) →
          1 - ε ≤ erProb n (C * Real.log n ^ ψ / n)
            (fun G => RandTreeUniv.IsLinkingSystemIn G Set.univ a b k) := by sorry

end RandTreeUniv.Supplement
