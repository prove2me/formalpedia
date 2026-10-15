-- Prove2me | Theorems.Thm_PosetSecretary_LowerBound_proposition_5_1
-- name    : PosetSecretary.LowerBound.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:14.41692+00:00
-- url     : https://prove2.me/theorems/29c72c21-b70b-44df-a99f-9f073ae4ea39
-- title:
--   Proposition 5.1, p. 14 (proof p. 42) — on a poset of width ω, every algorithm has sup over scorings of OPT/E[w(Alg)] ≥ ω
-- statement:
--   Let $k\ge1$ be the number of selections and $\omega\ge1$. There is a finite poset $\mathcal P$ of width $\omega$ such that for every selection rule $\mu$ with capacity $k$ on $\mathcal P$ and every $\varepsilon>0$ there is a scoring $w$ consistent with $\mathcal P$ with $\mathrm{OPT}(w,k)>0$ and
--   $$\mathbb E_\mu\big[w(\mathrm{Alg})\big]\le\frac{(1+\varepsilon)\,\mathrm{OPT}(w,k)}{\omega}.$$
--
--   Equivalently, for every algorithm $\mathcal A$, $\sup_{\mathcal I}\mathrm{OPT}(\mathcal I)/\mathbb E[w(\mathsf{Alg}(\mathcal I))]\ge\omega$, the supremum ranging over the scorings of $\mathcal P$. Here a scoring consistent with $\mathcal P$ is nonnegative, injective and strictly increasing along the order, $\mathrm{OPT}(w,k)$ is the largest total score of at most $k$ elements, and a selection rule with capacity $k$ is the law of the selected set: a probability distribution on subsets of at most $k$ elements.
--
--   Together with the upper bound $e^2(\omega+1)$ for ProxyLabel when the width is known (Corollary 5.1, p. 15), this shows that the width of the poset governs the best achievable competitive ratio.
--
--   **Formalization Note** The printed statement reads "there is an instance $\mathcal I=(\mathcal P,w)$ … such that $\mathrm{OPT}/\mathbb E\ge\omega$ for any algorithm" ($\exists\mathcal I\,\forall\mathcal A$); this order is false for $\omega\ge2$, since on a fixed instance the rule selecting the $k$ best elements has ratio $1$. The formalization follows the last sentence of the proof (Appendix F, p. 42): the poset is fixed first, then the algorithm and $\varepsilon$, then the scoring. Algorithms are encoded as score-independent distributions of the selected set; this class contains every online algorithm (which sees only the poset and the arrival order), so the bound holds for them. "$\alpha$-competitive" is read as $\mathrm{OPT}/\alpha\le\mathbb E$, avoiding a division by $\mathbb E$, which may be $0$. The hypotheses $k\ge1$ and $\omega\ge1$ are standing: with $\omega=0$ the poset is empty and with $k=0$ every ratio is $0/0$. Width is the largest antichain.
-- source:
--   Salem & Gupta, Secretary Problems with Biased Evaluations Using Partial Ordinal Information, SSRN 3444283 (version of 2022-04-17), Proposition 5.1, p. 14; proof in Appendix F, p. 42

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_LowerBound_Setting

namespace PosetSecretary.LowerBound

theorem proposition_5_1 (k ω : ℕ) (hk : 1 ≤ k) (hω : 1 ≤ ω) :
    ∃ (β : Type) (_ : PartialOrder β) (_ : Fintype β) (_ : DecidableEq β),
      AppliedComb.Posets.width β = ω ∧
      ∀ μ : Finset β → ℝ, IsSelectionRule k μ →
        ∀ ε : ℝ, 0 < ε →
          ∃ w : β → ℝ, PosetSecretary.ProxyLabel.IsConsistentScoring w ∧ 0 < PosetSecretary.ProxyLabel.opt w k ∧
            expectedScore μ w ≤ (1 + ε) * PosetSecretary.ProxyLabel.opt w k / ω := by sorry

end PosetSecretary.LowerBound
