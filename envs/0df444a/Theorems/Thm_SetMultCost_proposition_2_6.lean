-- Prove2me | Theorems.Thm_SetMultCost_proposition_2_6
-- name    : SetMultCost.proposition_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:53:49.341702+00:00
-- url     : https://prove2.me/theorems/9d76b350-e8c7-4ea8-acba-17aaf9758c87
-- title:
--   Proposition 2.6 (corrected: for balanced partitions) — full-rank projection of $\mathrm{IMM}_{n,d}$
-- statement:
--   Let $n=2^k$ and $n^\alpha=2^\ell$ with $1\le\ell\le k$, so $\alpha=\ell/k$, and let $d\ge1$. There is a balanced partition of $[d]$, and for every balanced partition $\pi=(\mathcal P,\mathcal N)$ there is a part-preserving projection $P_\alpha$ of $\mathrm{IMM}_{n,d}$ with
--
--   $$\mathrm{relrk}_{n,\alpha,\pi}(P_\alpha)\ge\frac{1}{n^{|\alpha d_{\mathcal P}-d_{\mathcal N}|/2}}.$$
--
--   Since the rank of a coefficient matrix is at most $\min(R,C)$, this is full rank: the bound is the largest possible value of the measure on these sizes.
--
--   Differences from the source:
--   - correction: "π as defined above", read as every partition → every balanced partition (`IsBalanced`), with the existence of one; reason: false for arbitrary π: n = 4, α = 1, d = 4, P = {1,2}, N = {3,4}; any ABP of width 4 has rank ≤ 4 at the middle cut, so relrk ≤ 1/4 < 1
--   - encoding: an ABP of width n → a part-preserving projection of IMM_{n,d}; reason: the last line of the proof of Corollary 2.7 identifies them
--   - encoding: k, ℓ ∈ N with n^α = 2^ℓ, α ∈ (0,1] → 1 ≤ ℓ ≤ k, with sizes 2^ℓ, 2^k and α = ℓ/k; reason: this is α ∈ (0,1] with k ≥ 1; n = 1 leaves α undefined
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Proposition 2.6, p.10

import Mathlib
import Definitions.Def_SetMultCost_imm
import Definitions.Def_SetMultCost_relrk
import Definitions.Def_SetMultCost_projection
import Definitions.Def_SetMultCost_IsBalanced

namespace SetMultCost

/-- **Proposition 2.6 (corrected).** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.10: "Assume that n = 2^k and n^α = 2^ℓ with k, ℓ ∈ N.
Then there is an ABP of width n that computes a polynomial Pα such that relrkn,α,π(Pα) ≥
1/n^{|αdP−dN|/2}".

**Formalization Note.** A correction: the page names no `π`, and for arbitrary `π` the statement is
false. At `n = 4`, `α = 1`, `d = 4`, `P = {1,2}`, `N = {3,4}`, any ABP of width `4` has rank at most
`4` across the middle cut, so relative rank at most `1/4`, while the right side is `1`. The statement
holds for every balanced `π` (`IsBalanced`), and such `π` exist. "ABP of width `n`" is a projection
of `IMM_{n,d}` (the last line of the proof of Corollary 2.7): every entry goes to a variable of its
own part or to `0`. The sizes are given as `2^ℓ` and `2^k`, and `α = ℓ/k`, so that `k ≥ 1`, and
`ℓ ≥ 1` is `α > 0`. -/
theorem proposition_2_6 (F : Type*) [Field F] (k ℓ d : ℕ) (hℓ : 1 ≤ ℓ) (hℓk : ℓ ≤ k) (hd : 1 ≤ d) :
    (∃ P : Finset (Fin d), IsBalanced k ℓ P) ∧
    ∀ P : Finset (Fin d), IsBalanced k ℓ P →
      ∃ ρ : IMMVar (2 ^ k) d → Option (Var d (sizeFn P (2 ^ ℓ) (2 ^ k))),
        IsPartPreserving Prod.fst Sigma.fst ρ ∧
        1 / ((2 : ℝ) ^ k) ^ (|((ℓ : ℝ) / k) * (P.card : ℝ) - (Pᶜ.card : ℝ)| / 2) ≤
          relrkAB (2 ^ ℓ) (2 ^ k) P Finset.univ (projection F ρ (imm F (2 ^ k) d)) := by sorry

end SetMultCost
