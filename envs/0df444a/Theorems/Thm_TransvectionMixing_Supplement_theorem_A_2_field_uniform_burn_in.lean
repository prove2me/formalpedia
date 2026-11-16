-- Prove2me | Theorems.Thm_TransvectionMixing_Supplement_theorem_A_2_field_uniform_burn_in
-- name    : TransvectionMixing.Supplement.theorem_A_2_field_uniform_burn_in
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:45:35.527346+00:00
-- url     : https://prove2.me/theorems/cc4c8816-3385-4599-92fe-6cabdee2c97c
-- title:
--   Theorem A.2 — field-uniform random-subset burn-in, $\Pr[\operatorname{rank}X_t[S]<k]\le\beta$ for $t\ge 60\frac{n^2}{n-k}\log\frac n\beta$
-- statement:
--   Let $\mathbb F_q$ be a finite field with $q$ elements ($q$ any prime power, with no lower bound), let $1\le k<n$, and let $\beta$ satisfy
--   $$0<\beta\le\tfrac1{10},\qquad \log(1/\beta)\le\frac{n-k}{288}.$$
--   Let $X_0\in\mathbb F_q^{n\times k}$ have full column rank $k$. Run the transvection walk from $X_0$: at each step $s=1,\dots,t$ draw an ordered pair $(I_s,J_s)$ of distinct rows uniformly and a coefficient $a_s\in\mathbb F_q$ uniformly, all independent, and set
--   $$X_t=(I_n+a_tE_{J_t,I_t})\cdots(I_n+a_1E_{J_1,I_1})\,X_0 .$$
--   Independently of the walk, choose a uniformly random row set $S\subseteq[n]$ of size
--   $$\ell=k+\big\lceil 4\log_q(1/\beta)\big\rceil ,$$
--   and let $X_t[S]$ be the $\ell\times k$ submatrix of $X_t$ formed by the rows in $S$. Then for every integer
--   $$t\ \ge\ 60\,\frac{n^2}{n-k}\,\log\frac n\beta$$
--   the rank-deficiency probability satisfies
--   $$\Pr_{X_0,S}\big[\operatorname{rank}X_t[S]<k\big]\le\beta .$$
--   Logarithms are natural and $\log_q x=\log x/\log q$.
--
--   This is the field-uniform burn-in of Appendix A: sampling slightly more than $k$ rows makes the sampled block full rank with high probability after $O\big(\frac{n^2}{n-k}\log\frac n\beta\big)$ steps, whatever the field size, whereas the fixed-row-set bound of Lemma 4.3 needs a large field.
--
--   **Formalization Note** The probability is the uniform normalized count `TransvectionMixing.prob` over the product of skeletons, coefficient vectors in $\mathbb F_q^t$ (zero included) and $\ell$-element subsets of `Fin n`, which is the joint law of the walk and the independent row set; $X_0$ is fixed and universally quantified. The walk matrix is the published `TransvectionMixing.walkMat`. The ceiling is `Nat.ceil`; its argument is positive under the hypotheses. The hypotheses force $\ell\le n$, so the set of $\ell$-subsets is nonempty (checked in a sanity file).
--
--   Differences from the source:
--   - encoding: q a prime power, 𝔽_q → an arbitrary finite field F with q = card F; reason: every finite field has prime-power order and every prime power is the order of a field, unique up to isomorphism, so the instances are the same.
--   - encoding: Pr_{X_0,S} over the walk and an independent uniform ℓ-set S → the uniform normalized count over Skel n t × (Fin t → F) × {S : Finset (Fin n) // S.card = ℓ}; reason: the walk's pairs and coefficients are independent and uniform (p.2), and S is independent and uniform, so the product counting measure is the joint law.
--   - encoding: ⌈4 log_q(1/β)⌉ → Nat.ceil (4 · (log(1/β) / log q)); reason: the argument is positive (β ≤ 1/10, q ≥ 2), where Nat.ceil equals the integer ceiling.
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Appendix A, Theorem A.2, (54), p.42; walk and skeleton §1, p.2

import Mathlib
import Definitions.Def_TransvectionMixing_walkMat

namespace TransvectionMixing.Supplement

/-- **Theorem A.2 (field-uniform random-subset burn-in)** of Braverman, Jain, Newman, *Optimal
Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields* (manuscript,
sha256 217f833f…), Appendix A, (54), p.42.

Let `F` be a finite field with `q = Fintype.card F` elements, `1 ≤ k < n`, `0 < β ≤ 1/10` with
`log(1/β) ≤ (n − k)/288`, and `X₀ ∈ F^{n×k}` of full column rank. Run the transvection walk
for `t` steps from `X₀` (uniform skeleton `σ` of ordered pairs of distinct rows, independent
uniform coefficients `a ∈ F^t`, so `X_t = walkMat σ a * X₀`) and independently draw a uniform
row set `S ⊆ [n]` of size `ℓ = k + ⌈4 log_q(1/β)⌉`. Then for every integer
`t ≥ 60 · n²/(n − k) · log(n/β)`, `Pr[rank X_t[S] < k] ≤ β`.

**Formalization Note** Rows are `Fin n` (0-based). The probability is the published uniform
normalized count `TransvectionMixing.prob` on the product `Skel n t × (Fin t → F) × ℓ-subsets`,
i.e. the joint law of the walk and the independent row set; `X₀` is fixed and universally
quantified. Coefficients range over all of `F`, zero included (p.2). `log` is the natural
logarithm and `log_q x = log x / log q`; the ceiling is `Nat.ceil` (its argument is positive
under the hypotheses, so it agrees with the integer ceiling). `n − k` is computed in `ℝ`.
`X_t[S]` is the `|S| × k` submatrix of the rows in `S`. No lower bound on `q` is assumed. -/
theorem theorem_A_2_field_uniform_burn_in
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 10)
    (hβn : Real.log (1 / β) ≤ ((n : ℝ) - k) / 288)
    (X₀ : Matrix (Fin n) (Fin k) F) (hX₀ : X₀.rank = k)
    (t : ℕ) (ht : 60 * ((n : ℝ) ^ 2 / ((n : ℝ) - k)) * Real.log (n / β) ≤ t) :
    prob (Ω := Skel n t × (Fin t → F) ×
        {S : Finset (Fin n) //
          S.card = k + ⌈4 * (Real.log (1 / β) / Real.log (Fintype.card F))⌉₊})
      (fun ω => ((walkMat ω.1 ω.2.1 * X₀).submatrix
        (fun i : ↥(ω.2.2.1) => (i : Fin n)) id).rank < k) ≤ β := by sorry

end TransvectionMixing.Supplement
