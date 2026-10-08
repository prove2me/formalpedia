-- Prove2me | Theorems.Thm_ThompsonAmenability_isAmenable_iff_isExtensivelyAmenableOn_P_bot_of_le_H_bot
-- name    : ThompsonAmenability.isAmenable_iff_isExtensivelyAmenableOn_P_bot_of_le_H_bot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:00:20.912533+00:00
-- url     : https://prove2.me/theorems/646a905e-c60e-4984-8258-3d9a0c5b8f6a
-- title:
--   Theorem 6.4 of Juschenko–Matte Bon–Monod–de la Salle on the breakpoints, for H(ℤ) — a subgroup of H(ℤ) is amenable if and only if its action on P_ℤ is extensively amenable
-- statement:
--   Let $K$ be a subgroup of the homeomorphisms of the projective line $\mathbf P^1 = \mathbb R \cup \{\infty\}$ contained in Monod's group $H(\mathbb Z)$ (`Monod.H ⊥`, where `⊥` is the smallest subring of $\mathbb R$, namely $\mathbb Z$). Then $K$ is amenable (`Garrido.IsAmenable K`) if and only if its action on $\mathbf P^1$ by evaluation is extensively amenable relative to $P_{\mathbb Z}$ (`IsExtensivelyAmenableOn K (OnePoint ℝ) (Monod.P ⊥)`), the set of fixed points in $\mathbf P^1$ of hyperbolic elements of $\mathrm{SL}_2(\mathbb Z)$, where the elements of $H(\mathbb Z)$ may break.
--
--   For $K = H(\mathbb Z)$ this restates Monod's Problem 12 ([`ThompsonAmenability.not_isAmenable_H_bot`](https://prove2.me/theorems/2c37d11c-772a-46f1-856a-3f0a903b2a38)): $H(\mathbb Z)$ is non-amenable if and only if its action on $P_{\mathbb Z}$ is not extensively amenable.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 23: “Theorem 6.4. A subgroup $H_1$ of $H$ is amenable if and only if $H_1 \curvearrowright \mathbf R$ is extensively amenable.” For the subgroups of $H(\mathbb Z)$ this statement asks for extensive amenability on $P_{\mathbb Z}$ in place of $\mathbb R$, and it implies the form on $\mathbb R$: [`ThompsonAmenability.isAmenable_iff_isExtensivelyAmenableOn_of_le_H_bot`](https://prove2.me/theorems/cdf118cc-b7fa-4599-9bd6-b88a5c27b1aa).
--
--   **Route.** The amenable direction holds for every action of an amenable group. For the other, let $c(g)(x) = \log g'_+(x) - \log g'_-(x)$, the jump of the logarithmic derivative of $g$ at $x$, supported in the breakpoints of $g$, hence in $P_{\mathbb Z}$; at $\infty$ record instead the translation by which $g$ acts near $\infty$. Then $c(gh) = c(g) + g_* c(h)$, and the affine action $\varphi \mapsto c(g) + g_*\varphi$ on the finitely supported real functions is free: an element fixing some $\varphi$ is the identity near $\infty$ and has zero jump at each of its fixed points, while at the right end $b$ of its support it would pass from a non-trivial element of $\mathrm{PSL}_2(\mathbb Z)$ fixing the irrational $b$, which is hyperbolic, to the identity, a non-zero jump. [`ThompsonAmenability.isAmenable_of_isExtensivelyAmenableOn_of_cocycle`](https://prove2.me/theorems/dd4dc306-5e82-47e1-8ed8-724ca46e62c8) then gives amenability.
-- source:
--   Standalone theorem: for subgroups of H(ℤ) (Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110), the form of Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 23, Theorem 6.4, with extensive amenability on the breakpoint set P_ℤ in place of ℝ

import Definitions.Def_Garrido_Amenability
import Definitions.Def_ThompsonAmenability
import Definitions.Def_Monod_PiecewiseProjective
import Definitions.Def_HomeomorphAction
import Mathlib

namespace ThompsonAmenability

theorem isAmenable_iff_isExtensivelyAmenableOn_P_bot_of_le_H_bot
    (K : Subgroup (OnePoint ℝ ≃ₜ OnePoint ℝ)) (hK : K ≤ Monod.H (⊥ : Subring ℝ)) :
    Garrido.IsAmenable K ↔ IsExtensivelyAmenableOn K (OnePoint ℝ) (Monod.P (⊥ : Subring ℝ)) := by
  sorry

end ThompsonAmenability
