-- Prove2me | Theorems.Thm_ThompsonAmenability_exists_foelner_P_bot
-- name    : ThompsonAmenability.exists_foelner_P_bot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:00:20.622222+00:00
-- url     : https://prove2.me/theorems/3f0f5e1a-d25e-4813-994a-a7b907786b97
-- title:
--   H(ℤ) acts amenably on P_ℤ — Følner sets inside p + ℤ for every finite subset of H(ℤ)
-- statement:
--   Let $p \in \mathbb R$ be a point of $P_{\mathbb Z}$ (`Monod.P ⊥`, the fixed points in $\mathbf P^1$ of hyperbolic elements of $\mathrm{SL}_2(\mathbb Z)$), let $S$ be a finite subset of Monod's group $H(\mathbb Z)$ (`Monod.H ⊥`), and let $\varepsilon > 0$. Then there is a nonempty finite set $A \subseteq P_{\mathbb Z}$ of points of the form $p + j$ with $j \in \mathbb Z$ such that $|sA \mathbin{\triangle} A| \le \varepsilon |A|$ for every $s \in S$, where $H(\mathbb Z)$ acts on $\mathbf P^1$ by evaluation.
--
--   This is the Følner condition for the action of $H(\mathbb Z)$ on $P_{\mathbb Z}$. Juschenko, Matte Bon, Monod and de la Salle prove the corresponding property for Monod's larger group on $\mathbb R$, p. 22: “Lemma 6.3. $H \curvearrowright \mathbf R$ is hereditarily amenable.” It matters for Monod's Problem 12 through [`ThompsonAmenability.isAmenable_iff_isExtensivelyAmenableOn_P_bot_of_le_H_bot`](https://prove2.me/theorems/646a905e-c60e-4984-8258-3d9a0c5b8f6a): non-amenability of $H(\mathbb Z)$ cannot come from a non-amenable action on $P_{\mathbb Z}$, only from the failure of extensive amenability.
--
--   **Route.** Near $\infty$ every element of $H(\mathbb Z)$ is a translation $x \mapsto x + n$ with $n \in \mathbb Z$, and $P_{\mathbb Z}$ is invariant under $x \mapsto x + 1$. So for $N$ large the sets $\{p + N, p + N + 1, \ldots, p + N + L\}$ are moved by each $s \in S$ only at their ends, and $L$ large makes $|sA \mathbin{\triangle} A| / |A|$ small.
-- source:
--   Standalone theorem: the action of H(ℤ) (Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110) on P_ℤ is amenable, compare Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 22, Lemma 6.3 (H ↷ ℝ is hereditarily amenable)

import Definitions.Def_Monod_PiecewiseProjective
import Definitions.Def_HomeomorphAction
import Mathlib

namespace ThompsonAmenability

open Classical in
theorem exists_foelner_P_bot {p : ℝ} (hp : (p : OnePoint ℝ) ∈ Monod.P (⊥ : Subring ℝ))
    (S : Finset (Monod.H (⊥ : Subring ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset (OnePoint ℝ), A.Nonempty ∧ (↑A : Set (OnePoint ℝ)) ⊆ Monod.P (⊥ : Subring ℝ) ∧
      (∀ x ∈ A, ∃ j : ℤ, x = ((p + j : ℝ) : OnePoint ℝ)) ∧
      ∀ s ∈ S, ((symmDiff (A.image (fun x => s • x)) A).card : ℝ) ≤ ε * A.card := by
  sorry

end ThompsonAmenability
