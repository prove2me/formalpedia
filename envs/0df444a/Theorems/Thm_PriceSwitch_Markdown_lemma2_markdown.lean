-- Prove2me | Theorems.Thm_PriceSwitch_Markdown_lemma2_markdown
-- name    : PriceSwitch.Markdown.lemma2_markdown
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:07:58.745241+00:00
-- url     : https://prove2.me/theorems/b3cefb94-2e9e-4d5b-812a-9a88b93963c1
-- title:
--   Lemma 2 — markdown threshold zeros and one sign change
-- statement:
--   Suppose the initial price $a$ exceeds the markdown price $b$, their Poisson rates satisfy $0<\lambda_a<\lambda_b$, and their revenue rates satisfy $a\lambda_a<b\lambda_b$. Define
--
--   $$
--   G(n,t)=a\lambda_a-b\lambda_b-b(\lambda_a-\lambda_b)\Pr\{\operatorname{Poisson}(\lambda_b t)\ge n\},\qquad
--   y_n=\inf\{s\ge0:G(n,s)=0\}.
--   $$
--
--   For every $n\ge1$ the defining zero exists. The thresholds satisfy $0<y_1<y_2<\cdots$. For each $n$, $G(n,s)<0$ on $0\le s<y_n$ and $G(n,s)>0$ on $s>y_n$. Thus there is exactly one sign change, from negative to positive.
--
--   The threshold and sign facts supply the base comparison used in the markdown result.
--
--   **Formalization Note** This states case (i) of Lemma 2; case (ii) belongs to the markup mission. The printed word “bounded” is a slip: $y_n$ grows without bound. The formal claim says the sequence is bounded away from zero and is strictly increasing. The nonempty zero set prevents a default value for the infimum. Positive prices and rates are the paper's working convention. Poisson tails use a nonnegative mean.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), Lemma 2 and preceding definitions, p. 1379, https://doi.org/10.1287/mnsc.41.8.1371

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.Markdown

/-- Feng–Gallego (1995), Lemma 2, case (i), p. 1379. The printed word "bounded" is corrected to
bounded away from zero: the thresholds tend to infinity. -/
theorem lemma2_markdown (a la b lb : ℝ) (hpair : IsMarkdownPair a la b lb) :
    let y : ℕ → ℝ := fun n => sInf {s : ℝ | 0 ≤ s ∧ G a la b lb n s = 0}
    (∀ n, 1 ≤ n → ∃ s, 0 ≤ s ∧ G a la b lb n s = 0) ∧
    0 < y 1 ∧
    StrictMonoOn y (Set.Ici 1) ∧
    (∀ n, 1 ≤ n → ∀ s, 0 ≤ s → s < y n → G a la b lb n s < 0) ∧
    (∀ n, 1 ≤ n → ∀ s, y n < s → 0 < G a la b lb n s) := by sorry

end PriceSwitch.Markdown
