-- Prove2me | Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_7
-- name    : SubsampleSubmod.SampleGreedy.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:02.43467+00:00
-- url     : https://prove2.me/theorems/a1e735d8-d879-4f28-a510-b9a71fbd3e15
-- title:
--   Lemma 7, p. 13 — with q = 1/(p+1), E[|O_u ∖ S| · f(u | S_u)] ≤ p/(p+1) · E[X_u f(u | S_u)] (5)
-- statement:
--   Let $(\mathcal N, \mathcal I)$ be a $p$-extendible independence system with $p \ge 1$, $T \in \mathcal I$ and $f$ a set function. Run Algorithm 2 from $O = T$ with every coin showing $1$ independently with probability $q = \frac{1}{p+1}$, and let $X_u$ indicate that $u$ is considered. Then for every element $u \in \mathcal N$,
--   $$\mathbb E\big[|O_u \setminus S| \cdot f(u \mid S_u)\big] \;\le\; \frac{p}{p+1}\,\mathbb E\big[X_u\, f(u \mid S_u)\big]. \tag{5}$$
--
--   This is where the choice $q = 1/(p+1)$ balances the elements of OPT that may be lost against the gains of the considered elements.
--
--   **Formalization Note** $|O_u \setminus S|$ is a natural number cast to $\mathbb R$; the expectations are exact sums over the $2^n$ coin outcomes.
-- source:
--   Harshaw et al., arXiv:2104.02772v1, p. 13, Lemma 7, inequality (5)

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis

namespace SubsampleSubmod.SampleGreedy

/-- Lemma 7 (p. 13), inequality (5). With sampling probability `q = 1/(p+1)`, for every element `u`:
`E[|O_u \ S| · f(u | S_u)] ≤ p/(p+1) · E[X_u f(u | S_u)]`, where `X_u` indicates that `u` is
considered by Algorithm 2 (run from an independent `T`, over a `p`-extendible system). -/
theorem lemma_7 {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hp : 1 ≤ p) (hI : IsIndepSystem I)
    (hext : IsPExtendible p I) (T : Finset α) (hT : I T) (u : α) :
    E2 (1 / ((p : ℝ) + 1)) f I T
        (fun st => ((st.Ou u \ st.S).card : ℝ) * marg f u (st.Su u)) ≤
      ((p : ℝ) / ((p : ℝ) + 1)) *
        E2 (1 / ((p : ℝ) + 1)) f I T
          (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u)) := by sorry

end SubsampleSubmod.SampleGreedy
