-- Prove2me | Theorems.Thm_ThompsonAmenability_isAmenable_iff_isExtensivelyAmenableOn_of_le_H_bot
-- name    : ThompsonAmenability.isAmenable_iff_isExtensivelyAmenableOn_of_le_H_bot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:00:48.418317+00:00
-- url     : https://prove2.me/theorems/cdf118cc-b7fa-4599-9bd6-b88a5c27b1aa
-- title:
--   Juschenko–Matte Bon–Monod–de la Salle, Theorem 6.4, for subgroups of H(ℤ) — amenable if and only if the action on ℝ is extensively amenable
-- statement:
--   Let $K$ be a subgroup of the homeomorphisms of the projective line $\mathbf P^1 = \mathbb R \cup \{\infty\}$ contained in Monod's group $H(\mathbb Z)$ (`Monod.H ⊥`, where `⊥` is the smallest subring of $\mathbb R$, namely $\mathbb Z$). Then $K$ is amenable (`Garrido.IsAmenable K`) if and only if its action on $\mathbf P^1$ by evaluation is extensively amenable relative to $\mathbb R \subseteq \mathbf P^1$ (`IsExtensivelyAmenableOn K (OnePoint ℝ) (Set.range (↑))`).
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 23: “Theorem 6.4. A subgroup $H_1$ of $H$ is amenable if and only if $H_1 \curvearrowright \mathbf R$ is extensively amenable.” This is the theorem for the subgroups $H_1$ that lie in $H(\mathbb Z)$; the theorem as printed, for every subgroup of $H$, is [`ThompsonAmenability.isAmenable_iff_isExtensivelyAmenableOn_of_le_Hpp`](https://prove2.me/theorems/4debdb5e-51fb-400a-9b80-e04451b86ceb).
--
--   **Route.** From [`ThompsonAmenability.isAmenable_iff_isExtensivelyAmenableOn_P_bot_of_le_H_bot`](https://prove2.me/theorems/646a905e-c60e-4984-8258-3d9a0c5b8f6a), which needs extensive amenability on the breakpoint set $P_{\mathbb Z}$ only: an invariant mean on the finite subsets of $\mathbb R$ pushes forward along $E \mapsto E \cap P_{\mathbb Z}$ to one on the finite subsets of $P_{\mathbb Z}$, since $K$ maps $P_{\mathbb Z}$ to itself. The other direction holds for every action of an amenable group.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 23, Theorem 6.4, for the subgroups of H(ℤ) ≤ H

import Definitions.Def_Garrido_Amenability
import Definitions.Def_ThompsonAmenability
import Definitions.Def_Monod_PiecewiseProjective
import Definitions.Def_HomeomorphAction
import Mathlib

namespace ThompsonAmenability

theorem isAmenable_iff_isExtensivelyAmenableOn_of_le_H_bot
    (K : Subgroup (OnePoint ℝ ≃ₜ OnePoint ℝ)) (hK : K ≤ Monod.H (⊥ : Subring ℝ)) :
    Garrido.IsAmenable K ↔
      IsExtensivelyAmenableOn K (OnePoint ℝ) (Set.range ((↑) : ℝ → OnePoint ℝ)) := by
  sorry

end ThompsonAmenability
