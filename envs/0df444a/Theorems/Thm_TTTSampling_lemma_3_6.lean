-- Prove2me | Theorems.Thm_TTTSampling_lemma_3_6
-- name    : TTTSampling.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:39:55.946536+00:00
-- url     : https://prove2.me/theorems/cad613b6-4cf1-443a-b2ce-807c24c7e422
-- title:
--   Lemma 3.6 — on $E_{\mathrm{restrict}}$, $|\mathcal G^{\mathrm{ret}}|\le R^2|\mathcal G|/M$
-- statement:
--   Let $R>0$, $M\ge1$, any oracle $\hat\mu$, any finite class $\mathcal G$ and $w\in\Sigma^{\le n}$. Let $E_{\mathrm{restrict}}$ be the event that Algorithm 2, called at $w$ with $\mathcal G$ and $M$, returns a multiset $\mathcal T$ containing a sequence of length less than $n$. Then on $E_{\mathrm{restrict}}$,
--
--   $$
--   |\mathcal G^{\mathrm{ret}}|\;\le\;\frac{R^2\,|\mathcal G|}{M}.
--   $$
--
--   With $M=\bar R\ge2R^2$ this halves the class whenever Algorithm 2 returns an incomplete sequence, the "progress" that bounds the number of iterations of Algorithm 3 (Lemma 3.9).
--
--   Differences from the source:
--   - reading: Algorithm 2 (Line 11's "for some $y$"; "If $\xi=1$, add $w_{i,t}$ to $\mathcal T$; set $\mathcal G^{\mathrm{ret}}\leftarrow\dots$") → `alg2`: the least violating $y$ in the order of $\Sigma$; both actions under $\xi=1$; coins clamped to $[0,1]$; a trial with undefined $\bar\eta(\cdot\mid v)$ ends with nothing added; reason: the printed line leaves $y$ unspecified; clamping and the fallback act only on unreachable states
--   - encoding: ratio tests $a/b \le M$, $a/b<1/M$, $1/R\le a/b\le R$ with $0/0=1$ (footnote 12) → multiplicative tests $a\le Mb$, $Ma<b$, $b\le Ra \wedge a\le Rb$; reason: realizes $a/0=\infty$ for $a>0$ and $0/0=1$ exactly; same instances
--   - encoding: "almost surely" / "on the event" → for every outcome of positive probability; reason: equivalent for a discrete distribution
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.6, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_TTTSampling_alg2

namespace TTTSampling

/-- **Lemma 3.6.** Fix any `w ∈ Σ^{≤n}` and `𝒢 ⊂ ∆(Σⁿ)`. Let `E_restrict` denote the event that
Algorithm 2 returns a set `𝒯` for which `𝒯 ∩ Σ^{<n} ≠ ∅`. Then on the event `E_restrict`, we have
`|𝒢^ret| ≤ R²|𝒢|/M`.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.6, printed
p.21 (PDF p.23).

**Formalization Note** Stated for every outcome of positive probability. Standing data: `R > 0`
(Assumption 3.1), `M ≥ 1` (Algorithm 2); any oracle and any class. -/
theorem lemma_3_6 {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (R : ℝ) (M : ℕ)
    (μh : List α → NNReal) (G : Finset (PMF (Fin n → α))) (w : List α)
    (hR : 0 < R) (hM : 1 ≤ M) (hw : w.length ≤ n) :
    ∀ o ∈ (alg2 R M μh w G).support, (∃ x ∈ o.1, x.length < n) →
      (o.2.1.card : ℝ) ≤ R ^ 2 * G.card / M := by sorry

end TTTSampling
