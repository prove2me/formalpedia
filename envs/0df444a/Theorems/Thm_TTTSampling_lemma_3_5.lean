-- Prove2me | Theorems.Thm_TTTSampling_lemma_3_5
-- name    : TTTSampling.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:17.101193+00:00
-- url     : https://prove2.me/theorems/d2f15a3e-00cc-4f8a-aee4-535dfff8027a
-- title:
--   Lemma 3.5 — the trials of Algorithm 2 follow the cut sets
-- statement:
--   Let $\mu^\star\in\mathcal G$ satisfy Assumption 3.1 with parameter $R$ for the oracle $\hat\mu$, let $M\ge1$, and let $w\in\Sigma^{\le n}$ with $\hat\mu(w)>0$. Run Algorithm 2 at $w$ with class $\mathcal G$ and parameter $M$. Then, with probability one, for every outer iteration $i$ and every stage $t\ge1$ that it reaches:
--
--   1. the final value of $w_{i,t}$ lies in $\mathcal N^{\mathrm{int}}_{\mathcal G,M,t}(w)\cup\mathcal N^{\mathrm{fin}}_{\mathcal G,M,t}(w)$;
--   2. the class $\mathcal G_{i,t}$ set on Line 16 equals $\mathcal G_t(w_{i,t})$ of (10).
--
--   Moreover, every node of the returned multiset $\mathcal T$ lies in $\mathcal N^{\mathrm{fin}}_{\mathcal G,M}(w)$.
--
--   This identifies the random walk of Algorithm 2 with the deterministic sets of §3.1, which is what makes its output distribution computable (Lemma 3.7).
--
--   **Formalization Note** "Almost surely" is "on every outcome of positive probability", and outer iteration $i$ is any trial record of the $M$ trials; stages are indexed from $1$.
--
--   Differences from the source:
--   - reading: Algorithm 2 is analysed for the classes it is called with in §3, which contain $\mu^\star$ → hypotheses $\mu^\star\in\mathcal G$ and Assumption 3.1 for $\mu^\star$; reason: the lemma is applied only with $\mathcal G=\mathcal F^j\ni\mu^\star$ (Lemmas 3.10–3.15); without $\mu^\star$ in the class the walk can reach nodes where $\bar\eta(\cdot\mid v)$ is undefined
--   - encoding: no hypothesis on $\hat\mu(w)$ → $\hat\mu(w)>0$; reason: at $\hat\mu(w)=0$ every ratio of Line 6 is $0/0$ and the sampling of Line 7 is undefined; only excludes undefined cases (every node Algorithm 3 calls Algorithm 2 on has $\hat\mu>0$)
--   - reading: Algorithm 2 (Line 11's "for some $y$"; "If $\xi=1$, add $w_{i,t}$ to $\mathcal T$; set $\mathcal G^{\mathrm{ret}}\leftarrow\dots$") → `alg2`: the least violating $y$ in the order of $\Sigma$; both actions under $\xi=1$; coins clamped to $[0,1]$; a trial with undefined $\bar\eta(\cdot\mid v)$ ends with nothing added; reason: the printed line leaves $y$ unspecified; clamping and the fallback act only on unreachable states
--   - encoding: ratio tests $a/b \le M$, $a/b<1/M$, $1/R\le a/b\le R$ with $0/0=1$ (footnote 12) → multiplicative tests $a\le Mb$, $Ma<b$, $b\le Ra \wedge a\le Rb$; reason: realizes $a/0=\infty$ for $a>0$ and $0/0=1$ exactly; same instances
--   - encoding: "almost surely" / "on the event" → for every outcome of positive probability; reason: equivalent for a discrete distribution
--   - reading: $\mathcal N^{\mathrm{fin}}_{\mathcal G,M}(w):=\mathcal N^{\mathrm{fin}}_{\mathcal G,M,t_0}(w)=\mathcal N^{\mathrm{fin}}_{\mathcal G,M,t_0+1}(w)=\cdots$ (p.22) → `NfinLim` $=\mathcal N^{\mathrm{fin}}_{\mathcal G,M,n-|w|+1}(w)$; reason: the stable value of the final sets, reached by $t=\max(1,n-|w|)$ (Lemma 3.4, corrected); at $|w|=n$ it is $\{w\}$, not $\mathcal N^{\mathrm{fin}}_{\mathcal G,M,0}(w)=\emptyset$
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.5, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_TTTSampling_Assumption31
import Definitions.Def_TTTSampling_cutHist
import Definitions.Def_TTTSampling_alg2

namespace TTTSampling

/-- **Lemma 3.5.** Fix any `i ∈ [M]` denoting the outer iteration in Algorithm 2. For any `t ≥ 1`,
the final value of `w_{i,t}` computed in Algorithm 2 is an element of
`𝒩^int_{𝒢,M,t}(w) ∪ 𝒩^fin_{𝒢,M,t}(w)`, and the candidate class `𝒢_{i,t}` defined in Line 16 is
exactly `𝒢_t(w_{i,t})` as defined in (10). Moreover, the set `𝒯` computed in Algorithm 2 satisfies
`𝒯 ⊂ 𝒩^fin_{𝒢,M}(w)` almost surely.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.5, printed
p.20 (PDF p.22).

**Formalization Note**
* The first two claims are stated for every trial record `tr` in every outcome of positive
  probability of the `M` trials, and for every stage `t` the trial reaches (the proof,
  p.21, "restricting attention to those values of t for which the ith outer-loop iteration
  actually reaches stage t"). In Lean `tr.finals[t-1]`, `tr.classes[t-1]` are 0-indexed, so stage
  `t + 1` is index `t`.
* Hypotheses from the setting of §3 (Algorithm 2 is called with a class containing `µ⋆`):
  `µ⋆ ∈ 𝒢`, Assumption 3.1 for `µ⋆`, and `µ̂(w) > 0` (without it the sampling of Line 7 is
  undefined at `w`). `M ≥ 1`, `w ∈ Σ^{≤n}`. -/
theorem lemma_3_5 {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (R : ℝ) (M : ℕ)
    (μh : List α → NNReal) (G : Finset (PMF (Fin n → α))) (w : List α) (μs : PMF (Fin n → α))
    (hM : 1 ≤ M) (hw : w.length ≤ n) (hμs : μs ∈ G) (hA : Assumption31 μs μh R)
    (hpos : 0 < (μh w : ℝ)) :
    (∀ L ∈ (alg2Trials R M μh w G).support, ∀ tr ∈ L,
      (∀ t : ℕ, ∀ x : List α, tr.finals[t]? = some x →
          x ∈ Nint R M μh G w (t + 1) ∪ Nfin R M μh G w (t + 1)) ∧
      (∀ t : ℕ, ∀ x : List α, ∀ H : Finset (PMF (Fin n → α)),
          tr.finals[t]? = some x → tr.classes[t]? = some H → H = Gt R M μh G w (t + 1) x)) ∧
    ∀ o ∈ (alg2 R M μh w G).support, ∀ x ∈ o.1, x ∈ NfinLim R M μh G w := by sorry

end TTTSampling
