-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_Supplement_lemma_B_6
-- name    : TransparencyTeamContracts.Submodular.Supplement.lemma_B_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:22:29.854012+00:00
-- url     : https://prove2.me/theorems/3fd7381a-b027-40f9-bc7d-42ad96ca6d39
-- title:
--   Lemma B.6 (used in the proof of Theorem B.1) — Exact supremum of small-cost ratio limits
-- statement:
--   For every $k\ge0$, $X\ge1$ other than $(k,X)=(0,1)$, positive feasible costs accumulate at zero and the feasible right-hand limit exists:
--   $$\lim_{c\downarrow0}R(c;k,X)=R_0(k,X)=1+\frac{k(X-1)}{(k+X)(k+X^2-X)}\le\frac98.$$
--   Moreover $R_0(2,2)=9/8$ and
--   $$\sup_{k\ge0,\ X\ge1,\ (k,X)\ne(0,1)}R_0(k,X)=\frac98.$$
--   The explicit nontriviality of the feasible right-hand filter prevents a limit over an empty domain from testifying vacuously. The excluded corner has zero full-revelation payoff, as the source specifies.
--
--   Differences from the source:
--   - encoding: the limit as c tends to zero within the feasible positive-denominator range, excluding k=0,X=1 → Tendsto along nhdsWithin of RatioDomain, with NeBot and the explicit R0 expression; reason: this expresses the same feasible right-hand limit and prevents an empty-filter or zero-denominator interpretation
--   - encoding: the supremum of these limits is 9/8, attained at k=X=2 → a uniform R0 upper bound, equality at (2,2), and the real sSup identity; reason: the value set is nonempty and bounded by the other conjuncts; the source proof explicitly supplies the limit formula and maximizing parameters
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Lemma B.6, printed p. 29 (PDF p. 31)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_SingleAgent

open Filter
open scoped Topology

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Lemma B.6, printed 29 / PDF 31. A nontrivial feasible right-hand filter is
explicit; the excluded k=0,X=1 corner has zero full-disclosure payoff. -/
theorem lemma_B_6 :
    (∀ k X : ℝ, 0 ≤ k → 1 ≤ X → (k, X) ≠ (0, 1) →
      NeBot (nhdsWithin 0 {c | RatioDomain k X c}) ∧
      Tendsto (fun c => R c k X) (nhdsWithin 0 {c | RatioDomain k X c}) (𝓝 (R0 k X)) ∧
      R0 k X ≤ (9 / 8 : ℝ)) ∧
    R0 2 2 = (9 / 8 : ℝ) ∧
    sSup {r : ℝ | ∃ k X : ℝ, 0 ≤ k ∧ 1 ≤ X ∧ (k, X) ≠ (0, 1) ∧ r = R0 k X} =
      (9 / 8 : ℝ) := by sorry

end TransparencyTeamContracts.Submodular.Supplement
