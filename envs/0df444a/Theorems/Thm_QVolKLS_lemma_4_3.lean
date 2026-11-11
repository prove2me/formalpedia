-- Prove2me | Theorems.Thm_QVolKLS_lemma_4_3
-- name    : QVolKLS.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:43.679204+00:00
-- url     : https://prove2.me/theorems/601e3903-a946-4d56-9bfb-47b970d35da4
-- title:
--   Lemma 4.3 — pilot estimates: $O(\log(m+1))$ samples per stage give $c_i\in[\mu_i/2,2\mu_i]$ for all $i$ w.p. $99/100$
-- statement:
--   There is an absolute constant $C>0$ such that for every $m\ge1$ there are a sample size $P\le C\log(m+1)$ and an estimator $\mathrm{est}:\mathbb R^P\to\mathbb R$ with the following property. Let $\pi_0,\dots,\pi_{m-1}$ be probability laws on a common finite set, $X_i>0$ observables, $\mu_i=\mathbb E_{\pi_i}[X_i]$, and suppose
--   $$
--   \mathbb E_{\pi_i}\big[(X_i/\mu_i)^2\big]\le4\qquad(0\le i<m).
--   $$
--   Let $\tilde X_i$ satisfy $|\tilde X_i(z)-X_i(z)|\le|X_i(z)|/16$ (for instance $\tilde X_i=X_i$). Draw independent samples $z_{i,1},\dots,z_{i,P}\sim\pi_i$ for every $i$ and put $c_i=\mathrm{est}(\tilde X_i(z_{i,1}),\dots,\tilde X_i(z_{i,P}))$. Then
--   $$
--   \Pr\big[c_i\in[\mu_i/2,\,2\mu_i]\ \text{for all } i<m\big]\ \ge\ \tfrac{99}{100}.
--   $$
--
--   The pilot estimates $c_i$ are the bridge scales that keep every probability fed to the product estimator above $1/32$.
--
--   **Formalization Note** The estimator is fixed before the laws and sees only the sampled values (the paper uses the median of batch means); the probability is the product-law mass of the event over the sample arrays.
--
--   Differences from the source:
--   - reading: P = O(log(m+1)) independent samples per stage i suffice to find c_i ∈ [µ_i/2, 2µ_i] → ∃ P ≤ C log(m+1) and one estimator of the P sampled values, fixed before the laws; reason: an estimator that could see π_i or µ_i would make the statement empty; the paper's estimator uses only the sampled values
--   - encoding: the exact clause and the clause with X̃_i → one statement for every X̃_i with |X̃_i − X_i| ≤ |X_i|/16; reason: X̃_i = X_i is such a choice, so the exact clause is included
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Lemma 4.3, p.35 (setting (30)–(31), pp.34–35)

import Mathlib

set_option autoImplicit false

namespace QVolKLS

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Lemma 4.3 (Pilot estimates)**,
p.35. Setting of §4.3 (p.34): laws `π_0, …, π_{m−1}` on a common finite set and positive observables
`X_i`, `µ_i = E_{π_i}[X_i]`.

There is an absolute `C > 0` such that for every `m ≥ 1` there are a sample size `P ≤ C log(m + 1)`
and one estimator `est : ℝ^P → ℝ` (fixed before the laws) with the following property. For all laws
`π_i` and positive `X_i` with `E_{π_i}[(X_i/µ_i)²] ≤ 4` for every `i < m`, and all values `X̃_i(z)` with
`|X̃_i(z) − X_i(z)| ≤ |X_i(z)|/16` (in particular `X̃_i = X_i`): drawing `P` independent samples
`z_{i,1}, …, z_{i,P}` from each `π_i` (all independent) and setting
`c_i = est(X̃_i(z_{i,1}), …, X̃_i(z_{i,P}))`, the event `c_i ∈ [µ_i/2, 2µ_i]` for all `i < m` has
probability at least `99/100`.

**Formalization Note.** The common finite set is any finite type `Ω`; the probability of the event is
the sum of the product weights `∏_{i,j} π_i(z_{i,j})` over the sample arrays `z : Fin m → Fin P → Ω`
in the event. The estimator sees only the `P` sampled values of stage `i` (it cannot see `π_i` or
`µ_i`); the paper's estimator is the median of batch means (p.36). The clause with `X̃` contains the
clause with `X` (take `X̃ = X`). -/
theorem lemma_4_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      ∃ (P : ℕ) (est : (Fin P → ℝ) → ℝ), (P : ℝ) ≤ C * Real.log ((m : ℝ) + 1) ∧
        ∀ (Ω : Type) [Fintype Ω] (π X Xt : Fin m → Ω → ℝ),
          (∀ i x, 0 ≤ π i x) → (∀ i, ∑ x, π i x = 1) → (∀ i x, 0 < X i x) →
          (∀ i, ∑ x, π i x * (X i x / ∑ y, π i y * X i y) ^ 2 ≤ 4) →
          (∀ i x, |Xt i x - X i x| ≤ |X i x| / 16) →
          99 / 100 ≤ ∑ z : Fin m → Fin P → Ω, (∏ i, ∏ j, π i (z i j)) *
            Set.indicator {z : Fin m → Fin P → Ω | ∀ i, est (fun j => Xt i (z i j)) ∈
              Set.Icc ((∑ y, π i y * X i y) / 2) (2 * ∑ y, π i y * X i y)} (fun _ => (1 : ℝ)) z := by sorry

end QVolKLS
