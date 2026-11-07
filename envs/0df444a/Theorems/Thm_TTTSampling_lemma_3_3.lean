-- Prove2me | Theorems.Thm_TTTSampling_lemma_3_3
-- name    : TTTSampling.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:45.735185+00:00
-- url     : https://prove2.me/theorems/f8fa4f55-b20f-4c51-9d8e-0f1b738245e0
-- title:
--   Lemma 3.3 — $\mathcal N^{\mathrm{int}}_{\mathcal G,M,t}(w)\cup\mathcal N^{\mathrm{fin}}_{\mathcal G,M,t}(w)$ is a simple $w$-cut
-- statement:
--   Let $R>0$, $M\ge1$, $\hat\mu:\Sigma^{\le n}\to\mathbb R_{\ge0}$ any oracle, $\mathcal G$ any finite class of distributions on $\Sigma^n$ and $w\in\Sigma^{\le n}$. Then for every $t\ge0$,
--
--   $$
--   \mathcal N^{\mathrm{int}}_{\mathcal G,M,t}(w)\cup\mathcal N^{\mathrm{fin}}_{\mathcal G,M,t}(w)\ \text{is a simple } w\text{-cut:}
--   $$
--
--   every leaf $v\in\Sigma^n$ with $v\succ w$ has exactly one node of this set on its path from $w$.
--
--   This is the structural fact behind the unbiasedness computation of Lemma 3.7 and the telescoping in Lemma 3.8.
--
--   Differences from the source:
--   - encoding: ratio tests $a/b \le M$, $a/b<1/M$, $1/R\le a/b\le R$ with $0/0=1$ (footnote 12) → multiplicative tests $a\le Mb$, $Ma<b$, $b\le Ra \wedge a\le Rb$; reason: realizes $a/0=\infty$ for $a>0$ and $0/0=1$ exactly; same instances
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.3, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_TTTSampling_cutHist

namespace TTTSampling

/-- **Lemma 3.3.** For each `t ≥ 0`, `𝒩^int_{𝒢,M,t}(w) ∪ 𝒩^fin_{𝒢,M,t}(w)` is a simple `w`-cut.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.3, printed
p.19 (PDF p.21).

**Formalization Note** The standing data of §3.1: `R > 0` (Assumption 3.1), `M ≥ 1`
(Algorithm 2), a node `w ∈ Σ^{≤n}`, any oracle `µ̂` and any finite class `𝒢`. -/
theorem lemma_3_3 {α : Type} [Fintype α] [DecidableEq α] {n : ℕ} (R : ℝ) (M : ℕ)
    (μh : List α → NNReal) (G : Finset (PMF (Fin n → α))) (w : List α)
    (hR : 0 < R) (hM : 1 ≤ M) (hw : w.length ≤ n) (t : ℕ) :
    IsSimpleCut n w (Nint R M μh G w t ∪ Nfin R M μh G w t) := by sorry

end TTTSampling
