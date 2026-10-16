-- Prove2me | Theorems.Thm_SubsetShrink_LowerBound_lemma_1
-- name    : SubsetShrink.LowerBound.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:51.78899+00:00
-- url     : https://prove2.me/theorems/610414c5-c026-456d-b2c3-baf390fd9808
-- title:
--   Lemma 1, p. 44 — max over s-sparse v ⊆ S with ‖Xv‖ = 1 of |ε⊤Xv| ≳ σγ_{2s}√(s log(eq/s)) w.h.p.
-- statement:
--   Let $X$ be a real $n\times p$ matrix with unit Euclidean columns, let $\epsilon\in\mathbb R^n$ have independent $N(0,\sigma^2)$ entries with $\sigma>0$, and let $\gamma_{2s}$ be the minimal $2s$-sparse eigenvalue of $X$. There are universal constants $\tilde c>0$ and $C>0$ such that the following holds. Let $S\subseteq\{1,\dots,p\}$ have cardinality $q$ and let $s$ be an integer in $[1,q]$. Then, with probability at least
--   $$
--   1-2\Big(\frac{eq}{s}\Big)^{-\tilde c\gamma_{2s}^2 s},
--   $$
--   there is $v\in\mathbb R^p$ with $\operatorname{supp}(v)\subseteq S$, $\|v\|_0\le s$ and $\|Xv\|=1$ such that
--   $$
--   |\epsilon^\top Xv|\ \ge\ C\,\sigma\,\gamma_{2s}\sqrt{s\log(eq/s)} .
--   $$
--
--   Equivalently, $\max_{\operatorname{supp}(v)\subseteq S,\ \|v\|_0\le s,\ \|Xv\|=1}|\epsilon^\top Xv|\gtrsim\sigma\gamma_{2s}\sqrt{s\log(eq/s)}$ with that probability. It is the probabilistic core of the lower bound for best subsets: the noise is strongly correlated with some sparse direction inside any large set of columns.
--
--   **Formalization Note** The universal constants $\tilde c$ and $C$ (the factor hidden in $\gtrsim$) are quantified before $n,p,X,\sigma,S,s$. "With probability at least $1-\eta$" is stated as the existence of a measurable set $A$ of noise vectors with $\mathbb P(A)\ge1-\eta$ on which the conclusion holds, under the law of $\epsilon$ with independent $N(0,\sigma^2)$ entries. The maximum is attained (the set of values $Xv$ is compact), so "the maximum is at least" is stated as "some admissible $v$ reaches". The printed $\operatorname{supp}(v)\subset S$ is read as $\subseteq$. $\gamma_{2s}$ is computed over all $2s$-sparse vectors of $\mathbb R^p$ ($B_0(2s)=\mathbb R^p$ when $2s\ge p$). Logarithms are natural and $e=\exp(1)$.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 44, Lemma 1; proof B.10, p. 46

import Mathlib
import Definitions.Def_SubsetShrink_LowerBound_Model

namespace SubsetShrink.LowerBound

/-- Lemma 1, p. 44: for `S ⊆ [p]` with `|S| = q` and an integer `s ∈ [1, q]`, with probability at least
`1 − 2(eq/s)^{−c̃ γ_{2s}² s}` some `v` with `supp v ⊆ S`, `‖v‖₀ ≤ s`, `‖Xv‖ = 1` has
`|ε⊤Xv| ≥ C σ γ_{2s} √(s log(eq/s))`; `c̃` and `C` are universal. -/
theorem lemma_1 :
    ∃ ct C : ℝ, 0 < ct ∧ 0 < C ∧
      ∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ : ℝ) (S : Finset (Fin p)) (s : ℕ),
        SubsetShrink.Events.UnitCols X → 0 < σ → 1 ≤ s → s ≤ S.card →
        ∃ A : Set (Fin n → ℝ), MeasurableSet A ∧
          (∀ ε ∈ A, ∃ v : Fin p → ℝ, supp v ⊆ S ∧ l0 v ≤ s ∧ SubsetShrink.Events.l2 (X.mulVec v) = 1 ∧
            C * σ * SubsetShrink.L2.gam X (2 * s) * Real.sqrt (s * Real.log (Real.exp 1 * S.card / s)) ≤
              |SubsetShrink.Events.dot ε (X.mulVec v)|) ∧
          1 - 2 * (Real.exp 1 * S.card / s) ^ (-(ct * SubsetShrink.L2.gam X (2 * s) ^ 2 * s)) ≤
            (SubsetShrink.Events.noiseLaw n σ A).toReal := by sorry

end SubsetShrink.LowerBound
