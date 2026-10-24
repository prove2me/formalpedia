-- Prove2me | Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_8
-- name    : SubsampleSubmod.SampleGreedy.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:52.816441+00:00
-- url     : https://prove2.me/theorems/b41db4c3-aa2c-496e-9ea2-2845ce37bb32
-- title:
--   Lemma 8, p. 14 — q · Σ_{u∈𝒩} E[X_u f(u | S_u)] ≤ E[f(S)]
-- statement:
--   Let $f$ be non-negative, $\mathcal I$ any family of sets, $T$ any set, and $q \in [0,1]$. Run Algorithm 2 from $O = T$ with every coin showing $1$ independently with probability $q$, and let $X_u$ indicate that $u$ is considered. Then
--   $$q \cdot \sum_{u \in \mathcal N} \mathbb E\big[X_u\, f(u \mid S_u)\big] \;\le\; \mathbb E[f(S)].$$
--
--   Each considered element is kept with probability $q$, and the value of $S$ is $f(\emptyset)$ plus the gains of the kept elements; this lemma converts the right-hand sides of Lemmas 7 and 10 back into the expected value of the output.
-- source:
--   Harshaw et al., arXiv:2104.02772v1, p. 14, Lemma 8

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis

namespace SubsampleSubmod.SampleGreedy

/-- Lemma 8 (p. 14). For non-negative `f` and sampling probability `q ∈ [0, 1]`:
`q · ∑_{u ∈ 𝒩} E[X_u f(u | S_u)] ≤ E[f(S)]` for Algorithm 2 (any comparison set `T`). -/
theorem lemma_8 {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (hf0 : ∀ S, 0 ≤ f S) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (T : Finset α) :
    q * ∑ u : α, E2 q f I T
        (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u)) ≤
      E2 q f I T (fun st => f st.S) := by sorry

end SubsampleSubmod.SampleGreedy
