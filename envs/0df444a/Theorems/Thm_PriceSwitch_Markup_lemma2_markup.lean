-- Prove2me | Theorems.Thm_PriceSwitch_Markup_lemma2_markup
-- name    : PriceSwitch.Markup.lemma2_markup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:39.204248+00:00
-- url     : https://prove2.me/theorems/95415552-c004-48a7-bda3-738b10b36daa
-- title:
--   Lemma 2, case (ii) — unique sign change and increasing roots
-- statement:
--   Consider a markup pair: $0<a<b$, $0<\lambda_b<\lambda_a$, and $b\lambda_b<a\lambda_a$. Define $G(n,t)=a\lambda_a-b\lambda_b-b(\lambda_a-\lambda_b)\Pr\{N_b(t)\ge n\}$ and $y_n=\inf\{t\ge0:G(n,t)=0\}$. For each $n\ge1$ the defining set is nonempty, $y_1>0$, and $(y_n)_{n\ge1}$ is strictly increasing. Moreover,
--
--   $$
--   G(n,t)>0\quad(0\le t<y_n),\qquad G(n,t)<0\quad(t>y_n).
--   $$
--
--   Thus every inventory level has one transition from positive to negative switching advantage, and the transition occurs later for larger inventories.
--
--   **Formalization Note** The paper's word “bounded” is inconsistent with $y_n\to\infty$; the statement records the positive lower bound used later. This is the case-(ii) half of the paper's lemma. The Poisson tail uses the independent count's Poisson law.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), §4.1, Lemma 2, p. 1379, https://doi.org/10.1287/mnsc.41.8.1371

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.Markup

/-- Feng–Gallego (1995), Lemma 2, case (ii), p. 1379. The printed word "bounded" is replaced
by bounded away from zero, as required by the surrounding text and the actual sign pattern. -/
theorem lemma2_markup (a la b lb : ℝ) (hpair : PriceSwitch.Markdown.IsMarkupPair a la b lb) :
    (∀ n : ℕ, 1 ≤ n → ∃ s : ℝ, 0 ≤ s ∧ PriceSwitch.Markdown.G a la b lb n s = 0) ∧
    0 < sInf {s : ℝ | 0 ≤ s ∧ PriceSwitch.Markdown.G a la b lb 1 s = 0} ∧
    StrictMonoOn (fun n : ℕ => sInf {s : ℝ | 0 ≤ s ∧ PriceSwitch.Markdown.G a la b lb n s = 0})
      (Set.Ici 1) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ s : ℝ, 0 ≤ s →
      s < sInf {u : ℝ | 0 ≤ u ∧ PriceSwitch.Markdown.G a la b lb n u = 0} → 0 < PriceSwitch.Markdown.G a la b lb n s) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ s : ℝ,
      sInf {u : ℝ | 0 ≤ u ∧ PriceSwitch.Markdown.G a la b lb n u = 0} < s → PriceSwitch.Markdown.G a la b lb n s < 0) := by sorry

end PriceSwitch.Markup
