-- Prove2me | Theorems.Thm_QueueScalp_Entry_pricing_problem
-- name    : QueueScalp.Entry.pricing_problem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:54.816054+00:00
-- url     : https://prove2.me/theorems/44b64960-2f5b-4653-9fe7-d4da4e5243b2
-- title:
--   Pricing reduction in proof of Proposition 2
-- statement:
--   For demand $\Lambda>0$, consider any nonnegative price and compatible single-scalper customer equilibrium with joining cutoff $c^S$ and buying cutoff $\tilde c$. The scalper's revenue is
--
--   $$P\lambda q=\frac{\Lambda^3(c^S)^2\tilde c(c^S-\tilde c)}{\mu^2(\mu-\Lambda\tilde c)}.$$
--
--   Conversely, each $\tilde c\in[0,c^S]$ at the equilibrium joining cutoff is realized by an equilibrium, with $P=\tilde c D^I((c^S-\tilde c)/c^S)$. Thus the price-and-equilibrium optimization is exactly the one-dimensional pricing problem displayed in the proof of Proposition 2.
--
--   **Formalization Note** The converse explicitly rules out treating the reduced formula merely as an upper bound on attainable revenue.
-- source:
--   Yang, Wang & Cui, A Model of Queue-Scalping, authors' manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3865), proof of Proposition 2, Online Appendix p. 2 (PDF 35), pricing-problem display

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model

namespace QueueScalp.Entry

theorem pricing_problem (P : Params) (hS : P.Standing) (Lam : ℝ)
    (hLam : 0 < Lam) :
    (∀ price lam q cS ct : ℝ, 0 ≤ price →
      IsCustEq P Lam price lam q cS ct →
      price * lam * q =
        Lam ^ 3 * cS ^ 2 * ct * (cS - ct) /
          (P.mu ^ 2 * (P.mu - Lam * ct))) ∧
    (∀ ct ∈ Set.Icc (0 : ℝ) (cSOf P Lam),
      ∃ price lam q : ℝ,
        price = ct * D P.mu (Lam * cSOf P Lam)
          ((cSOf P Lam - ct) / cSOf P Lam) ∧
        0 ≤ price ∧
        IsCustEq P Lam price lam q (cSOf P Lam) ct) := by sorry
end QueueScalp.Entry
