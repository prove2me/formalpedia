-- Prove2me | Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_6
-- name    : SubsampleSubmod.SampleGreedy.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:57.514711+00:00
-- url     : https://prove2.me/theorems/e7fac303-6a29-4471-a05c-7d6551e47782
-- title:
--   Lemma 6, p. 12 — f(S) ≥ f(S ∪ OPT) − Σ_{u∈𝒩} |O_u ∖ S| · f(u | S_u) for the final sets of Algorithm 2
-- statement:
--   Let $f$ be submodular, $(\mathcal N, \mathcal I)$ an independence system, $T \in \mathcal I$ (playing the role of OPT) and $B$ any outcome of the coins. For the final sets $S$, $O_u$ and $S_u$ of Algorithm 2 run from $O = T$,
--   $$f(S) \;\ge\; f(S \cup T) \;-\; \sum_{u \in \mathcal N} |O_u \setminus S| \cdot f(u \mid S_u).$$
--
--   This is the deterministic half of the analysis of SampleGreedy: it charges the loss relative to $S \cup \mathrm{OPT}$ to the marginal gains of considered elements.
--
--   **Formalization Note** No non-negativity of $f$ and no $p$-extendibility are assumed; the statement holds for every outcome of the coins.
-- source:
--   Harshaw et al., arXiv:2104.02772v1, p. 12, Lemma 6 (proof pp. 12–13)

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis

namespace SubsampleSubmod.SampleGreedy

/-- Lemma 6 (p. 12). For the final sets of Algorithm 2 run from an independent `T` (OPT) and any coin
flips `B`: `f(S) ≥ f(S ∪ T) − ∑_{u ∈ 𝒩} |O_u \ S| · f(u | S_u)`, for submodular `f`. -/
theorem lemma_6 {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (hsub : NonmonotoneSubmod.Shared.Submodular f) (hI : IsIndepSystem I)
    (T : Finset α) (hT : I T) (B : Finset α) :
    f ((alg2 f I T B).S ∪ T) -
        ∑ u : α, (((alg2 f I T B).Ou u \ (alg2 f I T B).S).card : ℝ) *
          marg f u ((alg2 f I T B).Su u) ≤
      f (alg2 f I T B).S := by sorry

end SubsampleSubmod.SampleGreedy
