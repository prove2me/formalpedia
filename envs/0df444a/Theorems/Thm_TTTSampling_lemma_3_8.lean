-- Prove2me | Theorems.Thm_TTTSampling_lemma_3_8
-- name    : TTTSampling.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:39:55.993225+00:00
-- url     : https://prove2.me/theorems/8fc4dc6a-1b6e-41e5-bfd6-6c27bd778ff1
-- title:
--   Lemma 3.8 — expected and almost-sure number of new oracle evaluations of one call of Algorithm 2
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $\mu^\star\in\mathcal G$ satisfy Assumption 3.1 with parameter $R$ for $\hat\mu$, let $M\ge2$, and let $w\in\Sigma^{\le n}$ with $\hat\mu(w)>0$. Suppose Algorithm 2 is called at $w$ with class $\mathcal G$ and parameter $M$ when the values of $\hat\mu$ at $w$ and at all its children $w\circ y$ are already cached. Let $V$ be the number of new oracle evaluations it makes. Then
--
--   $$
--   \mathbb E[V]\;\le\;C\,|\Sigma|\,R\,M^2\Bigl(\mathbb E\Bigl[\sum_{w'\in\mathcal T}\frac{\mu^\star(w')}{\hat\mu(w')}\,|w'|\Bigr]-\frac{\mu^\star(w)}{\hat\mu(w)}\,|w|\Bigr),
--   $$
--
--   and $V\le C\,|\Sigma|\,M\,n$ almost surely. The sum over $\mathcal T$ counts multiplicity.
--
--   The bracket is the expected increase of the weighted depth $W=\sum_x \frac{\mu^\star(x)}{\hat\mu(x)}|x|$ of the particle system, which is how Lemma 3.15 converts the cost of each call into a telescoping sum.
--
--   **Formalization Note** The cache is any set of nodes containing $w$ and its children; new evaluations are the nodes read outside it (caching convention, p.18).
--
--   Differences from the source:
--   - encoding: $O(\cdot)$ → one absolute constant $C>0$ quantified before all parameters; reason: the two $O(\cdot)$ hide absolute constants
--   - reading: Algorithm 2 is analysed for the classes it is called with in §3, which contain $\mu^\star$ → hypotheses $\mu^\star\in\mathcal G$ and Assumption 3.1 for $\mu^\star$; reason: the lemma is applied only with $\mathcal G=\mathcal F^j\ni\mu^\star$ (Lemmas 3.10–3.15); without $\mu^\star$ in the class the walk can reach nodes where $\bar\eta(\cdot\mid v)$ is undefined
--   - encoding: no hypothesis on $\hat\mu(w)$ → $\hat\mu(w)>0$; reason: at $\hat\mu(w)=0$ every ratio of Line 6 is $0/0$ and the sampling of Line 7 is undefined; only excludes undefined cases (every node Algorithm 3 calls Algorithm 2 on has $\hat\mu>0$)
--   - encoding: "the values of $\hat\mu$ at $w$ and all its children have already been obtained" → the cache is any set $Q\supseteq\{w\}\cup\{w\circ y\}$ and new evaluations are the read nodes outside $Q$; reason: the caching paragraph of p.18; the cache in the lemma is whatever has been obtained
--   - reading: Algorithm 2 (Line 11's "for some $y$"; "If $\xi=1$, add $w_{i,t}$ to $\mathcal T$; set $\mathcal G^{\mathrm{ret}}\leftarrow\dots$") → `alg2`: the least violating $y$ in the order of $\Sigma$; both actions under $\xi=1$; coins clamped to $[0,1]$; a trial with undefined $\bar\eta(\cdot\mid v)$ ends with nothing added; reason: the printed line leaves $y$ unspecified; clamping and the fallback act only on unreachable states
--   - encoding: ratio tests $a/b \le M$, $a/b<1/M$, $1/R\le a/b\le R$ with $0/0=1$ (footnote 12) → multiplicative tests $a\le Mb$, $Ma<b$, $b\le Ra \wedge a\le Rb$; reason: realizes $a/0=\infty$ for $a>0$ and $0/0=1$ exactly; same instances
--   - encoding: "almost surely" / "on the event" → for every outcome of positive probability; reason: equivalent for a discrete distribution
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.8, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_TTTSampling_Assumption31
import Definitions.Def_TTTSampling_tvDist
import Definitions.Def_TTTSampling_alg2

namespace TTTSampling

/-- **Lemma 3.8.** Suppose that `M ≥ 2` and that, when Algorithm 2 is called, the values of `µ̂` at
`w` and all its children have already been obtained (i.e., cached). Then the expected number of new
oracle evaluations of `µ̂` made by Algorithm 2 is bounded above by
`O(|Σ|·R·M²) · (𝔼[Σ_{w′∈𝒯} (µ⋆(w′)/µ̂(w′))·|w′|] − (µ⋆(w)/µ̂(w))·|w|)`. Moreover, the number of new
oracle evaluations is bounded almost surely by `O(|Σ|Mn)`.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Lemma 3.8, printed
p.24 (PDF p.26).

**Formalization Note**
* Both `O(·)` are one absolute constant `C`, chosen before all parameters.
* The cache is any set `Q ⊇ {w} ∪ {w∘y | y ∈ Σ}`; the new evaluations are `(reads \ Q).card`
  (caching convention, p.18). The sum over `𝒯` counts multiplicity.
* Hypotheses from the setting of §3: `µ⋆ ∈ 𝒢`, Assumption 3.1, `µ̂(w) > 0`, `w ∈ Σ^{≤n}`. -/
theorem lemma_3_8 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (R : ℝ) (M : ℕ) (μh : List α → NNReal)
        (G : Finset (PMF (Fin n → α))) (w : List α) (μs : PMF (Fin n → α))
        (Q : Finset (List α)),
        2 ≤ M → w.length ≤ n → μs ∈ G → Assumption31 μs μh R → 0 < (μh w : ℝ) →
        insert w (Finset.univ.image (fun y : α => w ++ [y])) ⊆ Q →
        expect (alg2 R M μh w G) (fun o => ((o.2.2 \ Q).card : ℝ)) ≤
            C * Fintype.card α * R * (M : ℝ) ^ 2 *
              (expect (alg2 R M μh w G)
                  (fun o => (o.1.map (fun x => prefixMass μs x / (μh x : ℝ) * x.length)).sum) -
                prefixMass μs w / (μh w : ℝ) * w.length) ∧
          ∀ o ∈ (alg2 R M μh w G).support,
            ((o.2.2 \ Q).card : ℝ) ≤ C * Fintype.card α * M * n := by sorry

end TTTSampling
