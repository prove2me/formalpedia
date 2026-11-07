-- Prove2me | Theorems.Thm_TTTSampling_lemma_3_7
-- name    : TTTSampling.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:19.970603+00:00
-- url     : https://prove2.me/theorems/bb4d933b-ece2-4314-83ab-2cb3e0270be1
-- title:
--   Lemma 3.7 — visit probabilities (14) and unbiasedness $\mathbb E[\mathrm{occ}(w',\mathcal T)]=\hat\mu(w')/\hat\mu(w)$ (15)
-- statement:
--   Let $\mu^\star\in\mathcal G$ satisfy Assumption 3.1 with parameter $R$ for $\hat\mu$, let $M\ge1$, and let $w\in\Sigma^{\le n}$ with $\hat\mu(w)>0$. Run Algorithm 2 at $w$ with class $\mathcal G$ and parameter $M$.
--
--   1. For every $t\ge1$, every $w'\in\mathcal S_{\mathcal G,M,t}(w)$ and every outer iteration $i\in[M]$, the probability of the event $\bar A_{i,t}(w')$ that iteration $i$ sets $w_{i,t}=w'$ at some point is
--   $$
--   \mathbb P\bigl(\bar A_{i,t}(w')\bigr)=\bar\eta_{t-1,p(w')}\bigl(w'\mid p(w')\bigr)\cdot\frac{\hat\mu(p(w'))}{\hat\mu(w)}, \tag{14}
--   $$
--   where $p(w')$ is the unique node of $\mathcal N^{\mathrm{int}}_{\mathcal G,M,t-1}(w)$ on the path from $w$ to $w'$ and $\bar\eta_{t-1,p(w')}$ is the mean of $\mathcal G_{t-1}(p(w'))$.
--   2. For every $w'\in\mathcal N^{\mathrm{fin}}_{\mathcal G,M}(w)$, the expected multiplicity of $w'$ in $\mathcal T$ is
--   $$
--   \mathbb E\bigl[\mathrm{occ}(w',\mathcal T)\bigr]=\frac{\hat\mu(w')}{\hat\mu(w)}. \tag{15}
--   $$
--
--   Identity (15) is the unbiasedness of Algorithm 2: the proposal $\bar\eta$ may differ from $\mu^\star$, but the acceptance probabilities correct it exactly. It drives the martingales of Lemmas 3.10 and 3.12.
--
--   **Formalization Note** (14) is stated for every $a\in\mathcal N^{\mathrm{int}}_{t-1}(w)$ with $a\preceq w'$; by Lemma 3.3 that is $p(w')$.
--
--   Differences from the source:
--   - reading: Algorithm 2 is analysed for the classes it is called with in §3, which contain $\mu^\star$ → hypotheses $\mu^\star\in\mathcal G$ and Assumption 3.1 for $\mu^\star$; reason: the lemma is applied only with $\mathcal G=\mathcal F^j\ni\mu^\star$ (Lemmas 3.10–3.15); without $\mu^\star$ in the class the walk can reach nodes where $\bar\eta(\cdot\mid v)$ is undefined
--   - encoding: no hypothesis on $\hat\mu(w)$ → $\hat\mu(w)>0$; reason: at $\hat\mu(w)=0$ every ratio of Line 6 is $0/0$ and the sampling of Line 7 is undefined; only excludes undefined cases (every node Algorithm 3 calls Algorithm 2 on has $\hat\mu>0$)
--   - encoding: $p(w')$, "the unique node of $\mathcal N^{\mathrm{int}}_{t-1}(w)$ on the path from $w$ to $w'$" → every $a\in\mathcal N^{\mathrm{int}}_{t-1}(w)$ with $a\preceq w'$; reason: by Lemma 3.3 there is exactly one such $a$
--   - reading: Algorithm 2 (Line 11's "for some $y$"; "If $\xi=1$, add $w_{i,t}$ to $\mathcal T$; set $\mathcal G^{\mathrm{ret}}\leftarrow\dots$") → `alg2`: the least violating $y$ in the order of $\Sigma$; both actions under $\xi=1$; coins clamped to $[0,1]$; a trial with undefined $\bar\eta(\cdot\mid v)$ ends with nothing added; reason: the printed line leaves $y$ unspecified; clamping and the fallback act only on unreachable states
--   - encoding: ratio tests $a/b \le M$, $a/b<1/M$, $1/R\le a/b\le R$ with $0/0=1$ (footnote 12) → multiplicative tests $a\le Mb$, $Ma<b$, $b\le Ra \wedge a\le Rb$; reason: realizes $a/0=\infty$ for $a>0$ and $0/0=1$ exactly; same instances
--   - reading: $\mathcal N^{\mathrm{fin}}_{\mathcal G,M}(w):=\mathcal N^{\mathrm{fin}}_{\mathcal G,M,t_0}(w)=\mathcal N^{\mathrm{fin}}_{\mathcal G,M,t_0+1}(w)=\cdots$ (p.22) → `NfinLim` $=\mathcal N^{\mathrm{fin}}_{\mathcal G,M,n-|w|+1}(w)$; reason: the stable value of the final sets, reached by $t=\max(1,n-|w|)$ (Lemma 3.4, corrected); at $|w|=n$ it is $\{w\}$, not $\mathcal N^{\mathrm{fin}}_{\mathcal G,M,0}(w)=\emptyset$
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.7, (14)–(15), p.22 (PDF p.24)

import Mathlib
import Definitions.Def_TTTSampling_Assumption31
import Definitions.Def_TTTSampling_tvDist
import Definitions.Def_TTTSampling_cutHist
import Definitions.Def_TTTSampling_alg2

namespace TTTSampling

/-- **Lemma 3.7**, (14) and (15). For any `t ≥ 1` and `w′ ∈ 𝒮_{𝒢,M,t}(w)`,
`ℙ(Ā_{i,t}(w′)) = η̄_{t−1,p(w′)}(w′ | p(w′)) · µ̂(p(w′))/µ̂(w)` (14). Moreover, for any
`w′ ∈ 𝒩^fin_{𝒢,M}(w)`, the expected number of occurrences of `w′` in the set `𝒯` constructed in
Algorithm 2 is `𝔼[occ(w′, 𝒯)] = µ̂(w′)/µ̂(w)` (15).

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.7, printed
p.22 (PDF p.24); `Ā_{i,t}(w′)` (p.22) is the event that outer iteration `i` sets `w_{i,t} = w′`
at some point.

**Formalization Note**
* `p(w′)` is "the unique node of `𝒩^int_{𝒢,M,t−1}(w)` on the path from `w` to `w′`" (p.22); (14)
  is stated for every `a ∈ 𝒩^int_{t−1}(w)` with `a ⪯ w′`, which by Lemma 3.3 is that node.
* `η̄_{t−1,a}(w′ | a) = η̄(w′)/η̄(a)` for the mean `η̄` of `𝒢_{t−1}(a)` (10).
* Outer iteration `i` is the entry `L[i]` (0-indexed, `i < M`) of the list of trial records.
* Hypotheses from the setting of §3: `µ⋆ ∈ 𝒢`, Assumption 3.1, `µ̂(w) > 0`, `M ≥ 1`,
  `w ∈ Σ^{≤n}`. -/
theorem lemma_3_7 {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (R : ℝ) (M : ℕ)
    (μh : List α → NNReal) (G : Finset (PMF (Fin n → α))) (w : List α) (μs : PMF (Fin n → α))
    (hM : 1 ≤ M) (hw : w.length ≤ n) (hμs : μs ∈ G) (hA : Assumption31 μs μh R)
    (hpos : 0 < (μh w : ℝ)) :
    (∀ t : ℕ, 1 ≤ t → ∀ w' ∈ Ssand R M μh G w t, ∀ a ∈ Nint R M μh G w (t - 1), a <+: w' →
      ∀ i : ℕ, i < M →
        prob (alg2Trials R M μh w G) (fun L => ∃ tr, L[i]? = some tr ∧ (t, w') ∈ tr.visits) =
          mixPrefix (Gt R M μh G w (t - 1) a) w' / mixPrefix (Gt R M μh G w (t - 1) a) a *
            ((μh a : ℝ) / (μh w : ℝ))) ∧
    ∀ w' ∈ NfinLim R M μh G w,
      expect (alg2 R M μh w G) (fun o => (o.1.count w' : ℝ)) = (μh w' : ℝ) / (μh w : ℝ) := by sorry

end TTTSampling
