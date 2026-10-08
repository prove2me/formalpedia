-- Prove2me | Theorems.Thm_SelfishRouting_Bicriteria_lemma_2_3
-- name    : SelfishRouting.Bicriteria.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:18.546982+00:00
-- url     : https://prove2.me/theorems/901d1b22-fd04-4384-87ec-4203d1531a25
-- title:
--   Lemma 2.3 — the cost of a Nash flow is $C(f) = \sum_i L_i(f) r_i$
-- statement:
--   Consider an instance with edge–route incidence matrix $A$ (entries $0$ or $1$), commodities $i = 1,\dots,k$ with rates $r_i > 0$, and edge latency functions $\ell_e$ that are nonnegative, nondecreasing and continuous on $[0,\infty)$. Let $f$ be a Nash flow. Then there are numbers $L_1(f),\dots,L_k(f)$ such that every route $P \in \mathcal P_i$ with $f_P > 0$ has latency $\ell_P(f) = L_i(f)$, and
--   $$
--   C(f) = \sum_{i=1}^{k} L_i(f)\, r_i .
--   $$
--
--   The paper states just before the lemma: "if $f$ is at Nash equilibrium then all $s_i$-$t_i$ flow paths … have equal latency, say $L_i(f)$". The lemma expresses the cost of a Nash flow through these common latencies; the proof of Theorem 3.1 starts from it.
--
--   **Formalization Note.** $L_i(f)$ is introduced existentially, as the page's "say $L_i(f)$", together with the property that defines it; no minimum over a possibly empty set is taken. Routes are $0/1$ incidence columns, continuity replaces differentiability (footnote 3), and the latency hypotheses are on $[0,\infty)$ only.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 7, Lemma 2.3 and the sentence preceding it

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model

namespace SelfishRouting.Bicriteria

/-- Lemma 2.3 (p. 7): all flow paths of commodity `i` of a Nash flow have a common latency
`L i`, and `C(f) = ∑ᵢ Lᵢ(f) rᵢ`. -/
theorem lemma_2_3 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (ℓ : Fin J → ℝ → ℝ) (rate : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hrate : ∀ i, 0 < rate i)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (x : Fin R → ℝ) (hx : IsNashFlow A s ℓ rate x) :
    ∃ L : Fin Sd → ℝ, (∀ r, 0 < x r → pathLatency A ℓ x r = L (s r)) ∧
      cost A ℓ x = ∑ i, L i * rate i := by sorry

end SelfishRouting.Bicriteria
