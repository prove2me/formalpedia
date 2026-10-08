-- Prove2me | Theorems.Thm_SelfishRouting_Linear_lemma_2_3
-- name    : SelfishRouting.Linear.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:04.645994+00:00
-- url     : https://prove2.me/theorems/944d7562-f74f-44ce-b04f-3bb43d8e24df
-- title:
--   Lemma 2.3 — the cost of a Nash flow is $C(f)=\sum_i L_i(f)\,r_i$
-- statement:
--   Under the standing assumptions (0/1 route incidences, positive rates $r_i>0$, latencies nonnegative, nondecreasing and continuous on $[0,\infty)$), let $f$ be a flow at Nash equilibrium. Then all $s_i$-$t_i$ routes carrying positive flow have a common latency $L_i(f)$, and
--   $$C(f)=\sum_{i=1}^{k} L_i(f)\,r_i .$$
--
--   This expresses the cost of an equilibrium through one latency per commodity; it is the bridge between equilibrium latencies and costs in the proof of Theorem 4.5.
--
--   **Formalization Note** $L_i(f)$ is stated existentially: there is a function $L$ on commodities such that every route $P$ with $f_P>0$ has $\ell_P(f)=L(i)$ for the commodity $i$ it serves, and $C(f)=\sum_i L(i)\,r_i$. Since $r_i>0$ and $f$ is feasible, each commodity has a used route, so $L$ is determined. Continuity replaces differentiability (footnote 3, p. 7); routes are $0/1$ incidence columns (a disclosed generalization).
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 7, Lemma 2.3 (with the preceding paragraph defining Lᵢ(f))

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model

namespace SelfishRouting.Linear

/-- Lemma 2.3 (p. 7): at a Nash flow all used routes of commodity `i` have a common latency
`L i`, and the cost is `C(f) = ∑ᵢ Lᵢ(f) rᵢ`. -/
theorem lemma_2_3 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (ℓ : Fin J → ℝ → ℝ) (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (x : Fin R → ℝ) (hx : SelfishRouting.Bicriteria.IsNashFlow A s ℓ rate x) :
    ∃ L : Fin Sd → ℝ, (∀ r, 0 < x r → SelfishRouting.Bicriteria.pathLatency A ℓ x r = L (s r)) ∧
      SelfishRouting.Bicriteria.cost A ℓ x = ∑ i, L i * rate i := by sorry

end SelfishRouting.Linear
