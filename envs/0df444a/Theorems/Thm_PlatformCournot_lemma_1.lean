-- Prove2me | Theorems.Thm_PlatformCournot_lemma_1
-- name    : PlatformCournot.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:22.938988+00:00
-- url     : https://prove2.me/theorems/a6f63ced-47c7-4d18-b074-a751cf7febd9
-- title:
--   Lemma 1 — the networked Cournot game has a unique Nash equilibrium, the unique maximizer of (9)
-- statement:
--   Let $\mathcal E\subseteq F\times M$ be any edge set and let $C$ be a cost profile satisfying Assumption 1, with affine inverse demand $p_j(d)=\alpha_j-\beta_j d$, $\alpha_j,\beta_j>0$. Then
--
--   1. the networked Cournot game $(F,Q(\mathcal E),\pi)$ has exactly one pure strategy Nash equilibrium $q^{\mathrm{NE}}(\mathcal E)$;
--   2. a profile is a Nash equilibrium if and only if it is an optimal solution of the convex program
--
--   $$\max_{q\in Q(\mathcal E)}\ \mathrm{SW}(q,C)-\sum_{i=1}^n\sum_{j=1}^m\frac{\beta_j q_{ij}^2}{2}. \tag{9}$$
--
--   In particular (9) has a unique optimal solution, and it is the Nash equilibrium. The paper attributes the lemma to Abolhassani et al. (2014) and uses it to speak of "the" equilibrium of every game it considers.
--
--   Differences from the source:
--   - encoding: firms 1, …, n and markets 1, …, m → Fin n and Fin m (0-based), supply profile q i j firm first; reason: relabelling only
--   - encoding: "admits a unique Nash equilibrium that is the unique optimal solution to (9)" → ∃! Nash equilibrium, and Nash equilibrium ↔ maximizer of (9) over Q(ℰ); reason: the two clauses together say the equilibrium exists, is unique, and coincides with the (hence unique) optimal solution
--   - generalization: n firms and m markets, with n, m ≥ 1 implicit → every n and m in ℕ, including n = 0 and m = 0; reason: the added instances are degenerate, with a single trivial profile; every instance with n, m ≥ 1 is the page's
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Lemma 1, p.12

import Mathlib
import Definitions.Def_PlatformCournot_Assumption1
import Definitions.Def_PlatformCournot_IsNash
import Definitions.Def_PlatformCournot_potential
import Definitions.Def_PlatformCournot_feasibleProfiles

namespace PlatformCournot

/-- **Lemma 1 (Abolhassani et al. 2014): unique Nash equilibrium, the unique maximizer of (9).**
Pang et al., arXiv:1903.04574v3, Lemma 1, p.12: "The game (F,Q(ℰ),π) admits a unique Nash
equilibrium qNE(ℰ) ∈ Q(ℰ) that is the unique optimal solution to the following convex program:
maximize_{q∈Q(ℰ)} SW(q,C) − Σ_{i=1}^n Σ_{j=1}^m βj q²ij / 2. (9)"

For every edge set `ℰ` and every cost profile satisfying Assumption 1: there is exactly one Nash
equilibrium, and a profile is a Nash equilibrium iff it maximizes the objective (9) over `Q(ℰ)`
(so the maximizer of (9) is unique as well).

**Formalization Note** Firms `Fin n`, markets `Fin m`, profiles `q i j`; the price is affine and
untruncated. The paper cites the lemma without proof. -/
theorem lemma_1 {n m : ℕ} (D : AffineDemand m) (C : Fin n → ℝ → ℝ) (hC : Assumption1 C)
    (E : Set (Fin n × Fin m)) :
    (∃! q, IsNash D C E q) ∧
      ∀ q, IsNash D C E q ↔
        (q ∈ feasibleProfiles E ∧ ∀ q' ∈ feasibleProfiles E, potential D C q' ≤ potential D C q) := by sorry

end PlatformCournot
