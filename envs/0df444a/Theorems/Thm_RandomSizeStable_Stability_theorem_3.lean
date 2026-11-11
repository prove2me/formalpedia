-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_theorem_3
-- name    : RandomSizeStable.Stability.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:59.219431+00:00
-- url     : https://prove2.me/theorems/ee004649-f431-49b1-bc7f-68f6ee56a078
-- title:
--   Theorem 3 — existence, sharp benchmark and support equality
-- statement:
--   Let $D$ be any positive-integer draw law and $\mu_D=\mathbb E[1/(D+1)]$. Every finite nonempty strict-ranking profile $E$ admits a lottery $P$ such that
--   $$\forall c\in C,\quad L_c(P)\le\mu_D.$$
--   No smaller benchmark works for all profiles: for every real $\alpha<\mu_D$ there is a finite nonempty unweighted profile $E$ such that every lottery $Q$ has some candidate $c$ with $L_c(Q)>\alpha$. Finally, for every stable lottery on every profile, each candidate in its support satisfies
--   $$P(c)>0\quad\Longrightarrow\quad L_c(P)=\mu_D.$$
--   The support assertion is universal over stable lotteries, rather than a property of only one selected witness.
--
--   This guarantees that stability defines a nonempty class and fixes its best universal comparison level.
--
--   Differences from the source:
--   - encoding: finite nonempty voter and candidate sets with strict rankings → finite nonempty types and Election strict total orders; reason: these represent exactly the finite profiles in Section 2, with uniform voter averaging
--   - encoding: a positive-integer-valued random variable D → a PMF on the positive integers; reason: only the law enters these claims; countably infinite support and infinite mean remain allowed
--   - encoding: a finite profile witnessing failure of a smaller benchmark → positive sizes n,m and a profile on Fin n, Fin m; reason: every finite unweighted profile can be relabeled this way
-- source:
--   Nisarg Shah, Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission #1342 (October 2026), p. 10, Theorem 3.

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankBlocks

set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion

namespace RandomSizeStable.Stability

/-- Theorem 3, p.10: existence, universal sharpness, and support equality for
EVERY stable lottery. Sharpness uses finite nonempty unweighted profiles. -/
theorem theorem_3 (D : PMF ℕ+) :
    (∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
      (E : Election V C), ∃ P : C → ℝ, IsStable D E P) ∧
    (∀ α : ℝ, α < benchmark D →
      ∃ (n m : ℕ) (_ : 0 < n) (_ : 0 < m) (E : Election (Fin n) (Fin m)),
        ∀ P ∈ stdSimplex ℝ (Fin m), ∃ c, α < score D E P c) ∧
    (∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
      (E : Election V C) (P : C → ℝ), IsStable D E P →
        ∀ c, 0 < P c → score D E P c = benchmark D) := by sorry

end RandomSizeStable.Stability
