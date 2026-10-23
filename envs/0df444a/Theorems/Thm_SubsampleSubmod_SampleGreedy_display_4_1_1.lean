-- Prove2me | Theorems.Thm_SubsampleSubmod_SampleGreedy_display_4_1_1
-- name    : SubsampleSubmod.SampleGreedy.display_4_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:15.715486+00:00
-- url     : https://prove2.me/theorems/25f148be-3c92-49f4-977b-2687ff76c9ca
-- title:
--   §4.1.1, p. 14 — with q = 1/(p+1), E[f(S)] ≥ E[f(S ∪ OPT)] − Σ E[|O_u∖S| f(u|S_u)] ≥ … ≥ E[f(S ∪ OPT)] − p · E[f(S)]
-- statement:
--   Let $f$ be non-negative and submodular, $(\mathcal N, \mathcal I)$ a $p$-extendible independence system with $p \ge 1$, and $T \in \mathcal I$. Run Algorithm 2 from $O = T$ with sampling probability $q = \frac1{p+1}$. Then the chain of the proof of Theorem 1 for submodular objectives holds:
--   $$\begin{aligned}
--   \mathbb E[f(S)] &\ge \mathbb E[f(S\cup T)] - \sum_{u \in \mathcal N} \mathbb E\big[|O_u \setminus S|\cdot f(u\mid S_u)\big] \\
--   &\ge \mathbb E[f(S\cup T)] - \frac{p}{p+1}\sum_{u\in\mathcal N} \mathbb E\big[X_u\, f(u \mid S_u)\big] \\
--   &\ge \mathbb E[f(S\cup T)] - p\,\mathbb E[f(S)].
--   \end{aligned}$$
--
--   Combined with $\mathbb E[f(S \cup \mathrm{OPT})] \ge f(\mathrm{OPT})$ (monotone case) or $\mathbb E[f(S\cup\mathrm{OPT})] \ge (1 - q) f(\mathrm{OPT})$ (Lemma 3), and with Lemma 4, it yields the ratios $p+1$ and $(p+1)^2/p$ of Theorem 1.
--
--   **Formalization Note** The three inequalities of the display are stated as a conjunction, in the order printed.
-- source:
--   Harshaw et al., arXiv:2104.02772v1, p. 14, §4.1.1 (unnumbered display in the proof of Theorem 1, submodular objectives)

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis

namespace SubsampleSubmod.SampleGreedy

/-- The display of §4.1.1 (p. 14). With `q = 1/(p+1)`, for Algorithm 2 run from an independent `T`
(OPT), non-negative submodular `f` and a `p`-extendible system:
`E[f(S)] ≥ E[f(S ∪ T)] − ∑_u E[|O_u \ S| · f(u | S_u)]
  ≥ E[f(S ∪ T)] − p/(p+1) ∑_u E[X_u · f(u | S_u)] ≥ E[f(S ∪ T)] − p · E[f(S)]`. -/
theorem display_4_1_1 {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hp : 1 ≤ p) (hf0 : ∀ S, 0 ≤ f S)
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (hI : IsIndepSystem I)
    (hext : IsPExtendible p I) (T : Finset α) (hT : I T) :
    E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f (st.S ∪ T)) -
        ∑ u : α, E2 (1 / ((p : ℝ) + 1)) f I T
          (fun st => ((st.Ou u \ st.S).card : ℝ) * marg f u (st.Su u)) ≤
      E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f st.S) ∧
    E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f (st.S ∪ T)) -
        ((p : ℝ) / ((p : ℝ) + 1)) * ∑ u : α, E2 (1 / ((p : ℝ) + 1)) f I T
          (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u)) ≤
      E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f (st.S ∪ T)) -
        ∑ u : α, E2 (1 / ((p : ℝ) + 1)) f I T
          (fun st => ((st.Ou u \ st.S).card : ℝ) * marg f u (st.Su u)) ∧
    E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f (st.S ∪ T)) -
        (p : ℝ) * E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f st.S) ≤
      E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f (st.S ∪ T)) -
        ((p : ℝ) / ((p : ℝ) + 1)) * ∑ u : α, E2 (1 / ((p : ℝ) + 1)) f I T
          (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u)) := by sorry

end SubsampleSubmod.SampleGreedy
