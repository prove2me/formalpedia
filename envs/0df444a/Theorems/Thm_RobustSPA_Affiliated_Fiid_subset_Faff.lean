-- Prove2me | Theorems.Thm_RobustSPA_Affiliated_Fiid_subset_Faff
-- name    : RobustSPA.Affiliated.Fiid_subset_Faff
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T09:06:47.10788+00:00
-- url     : https://prove2.me/theorems/258865e5-5858-4fc3-b84f-545aa57598b4
-- title:
--   p. 19 — i.i.d. laws are exchangeable and affiliated: 𝓕_iid ⊆ 𝓕_aff
-- statement:
--   Let $n\ge 0$ and let $G$ be a probability law on $\mathbb R$ supported on $[0,1]$. Then the law $G^{\otimes n}$ of $n$ i.i.d. valuations drawn from $G$ is exchangeable and affiliated:
--   $$\mathcal F_{\mathrm{iid}}\subseteq\mathcal F_{\mathrm{aff}} .$$
--   Concretely, $G^{\otimes n}$ is a probability law on $[0,1]^n$, it is invariant under every permutation of the coordinates, and for all measurable increasing sets $A,B\subseteq\mathbb R^n$ and every measurable sublattice $S\subseteq\mathbb R^n$ (closed under coordinatewise $\min$ and $\max$),
--   $$G^{\otimes n}(A\cap S)\,G^{\otimes n}(B\cap S)\ \le\ G^{\otimes n}(A\cap B\cap S)\,G^{\otimes n}(S),$$
--   which is Definition 4, $\Pr(A\cap B\mid S)\ge\Pr(A\mid S)\Pr(B\mid S)$, cleared of denominators.
--
--   The affiliation part is the FKG / Harris inequality for product measures (equivalently, the Ahlswede–Daykin four-functions theorem on $\mathbb R^n$ with a product measure). It gives the inequality $\mathcal R^*_n(\mathcal F_{\mathrm{aff}})\ge\mathcal R^*_n(\mathcal F_{\mathrm{iid}})$ in the paper and, in the proof of Proposition 2, the membership of the worst-case i.i.d. law $F^*_n$ in $\mathcal F_{\mathrm{aff}}$.
--
--   **Formalization Note.** $\mathcal F_{\mathrm{iid}}$ is `RobustSPA.IID.Fiid` and $\mathcal F_{\mathrm{aff}}$ is `RobustSPA.Affiliated.Faff` (exchangeable laws in $\mathcal F_{\mathrm{all}}$ satisfying the cross-multiplied affiliation inequality).
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 19, sentence after Definition 4: "Clearly $\mathcal F_{\mathrm{iid}}\subset\mathcal F_{\mathrm{aff}}$ and hence $\mathcal R^*_n(\mathcal F_{\mathrm{aff}})\ge\mathcal R^*_n(\mathcal F_{\mathrm{iid}})$"

import Mathlib
import Definitions.Def_RobustSPA_Affiliated_Setting

namespace RobustSPA.Affiliated

open MeasureTheory RobustSPA.IID

theorem Fiid_subset_Faff (n : ℕ) : Fiid n ⊆ Faff n := by sorry

end RobustSPA.Affiliated
