-- Prove2me | Theorems.Thm_TTTSampling_lemma_3_4
-- name    : TTTSampling.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:39:02.709197+00:00
-- url     : https://prove2.me/theorems/6aa3733a-c842-4021-a1c7-b37d5608b729
-- title:
--   Lemma 3.4 (corrected: $t_0\le\max(1,n-|w|)$) — intermediate sets are empty from some $t_0$ on
-- statement:
--   Let $R>0$, $M\ge1$, any oracle $\hat\mu$, any finite class $\mathcal G$ and $w\in\Sigma^{\le n}$. There is $t_0\le\max(1,n-|w|)$ (that is, $t_0\le n-|w|$ whenever $|w|<n$) such that for all $t\ge t_0$,
--
--   $$
--   \mathcal N^{\mathrm{int}}_{\mathcal G,M,t}(w)=\emptyset\quad\text{and}\quad \mathcal N^{\mathrm{fin}}_{\mathcal G,M,t}(w)=\mathcal N^{\mathrm{fin}}_{\mathcal G,M,t_0}(w).
--   $$
--
--   So the final sets stabilize after at most $\max(1,n-|w|)$ stages, which makes $\mathcal N^{\mathrm{fin}}_{\mathcal G,M}(w)$ well defined.
--
--   Differences from the source:
--   - correction: $t_0\le n-|w|$ → $t_0\le\max(1,n-|w|)$; reason: the printed bound is false at $|w|=n$, which Algorithm 2 allows ($w\in\Sigma^{\le n}$; the proof of Lemma 3.8 treats $|w|=n$): $t_0=0$ would need $\mathcal N^{\mathrm{int}}_{\mathcal G,M,0}(w)=\{w\}=\emptyset$; the sets are empty from $t=1$ on; for $|w|<n$ this is the printed statement
--   - encoding: ratio tests $a/b \le M$, $a/b<1/M$, $1/R\le a/b\le R$ with $0/0=1$ (footnote 12) → multiplicative tests $a\le Mb$, $Ma<b$, $b\le Ra \wedge a\le Rb$; reason: realizes $a/0=\infty$ for $a>0$ and $0/0=1$ exactly; same instances
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.4, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_TTTSampling_cutHist

namespace TTTSampling

/-- **Lemma 3.4** (corrected: `t₀ ≤ max(1, n − |w|)`). There is some `t₀ ≤ n − |w|` so that for all `t ≥ t₀`,
`𝒩^int_{𝒢,M,t}(w) = ∅`, and therefore `𝒩^fin_{𝒢,M,t₀}(w) = 𝒩^fin_{𝒢,M,t₀+1}(w) = ⋯`.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.4, printed
p.20 (PDF p.22).

**Formalization Note**
* Standing data of §3.1: `R > 0`, `M ≥ 1`, `w ∈ Σ^{≤n}`.
* **Correction.** The bound is `t₀ ≤ max(1, n − |w|)`. As printed (`t₀ ≤ n − |w|`) the lemma is
  false for `|w| = n`, which Algorithm 2 allows (`w ∈ Σ^{≤n}`; the proof of Lemma 3.8 treats
  `|w| = n`): then `t₀ = 0` and `t = 0` would need `𝒩^int_0(w) = {w} = ∅`. The proof's step "no
  intermediate node can be a leaf" holds only for `t ≥ 1`; the sets are empty from `t = 1` on.
  For `|w| < n` the statement is the printed one. -/
theorem lemma_3_4 {α : Type} [Fintype α] [DecidableEq α] {n : ℕ} (R : ℝ) (M : ℕ)
    (μh : List α → NNReal) (G : Finset (PMF (Fin n → α))) (w : List α)
    (hR : 0 < R) (hM : 1 ≤ M) (hw : w.length ≤ n) :
    ∃ t₀ : ℕ, t₀ ≤ max 1 (n - w.length) ∧
      ∀ t : ℕ, t₀ ≤ t → Nint R M μh G w t = ∅ ∧ Nfin R M μh G w t = Nfin R M μh G w t₀ := by sorry

end TTTSampling
