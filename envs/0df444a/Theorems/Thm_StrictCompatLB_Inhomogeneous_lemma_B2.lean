-- Prove2me | Theorems.Thm_StrictCompatLB_Inhomogeneous_lemma_B2
-- name    : StrictCompatLB.Inhomogeneous.lemma_B2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:04:10.729341+00:00
-- url     : https://prove2.me/theorems/7d9a7092-db79-4d3b-9437-fcbb053ed1d6
-- title:
--   Lemma B.2 — inhomogeneous random graphs with $\bar p(N) = \omega((\ln M(N) + \ln N)/N)$ and $\|p(N)^{-1}\|_2^{-2} = \omega(\ln N/M(N)^2)$ are a.s. subcritical
-- statement:
--   Let $d \ge 2$, $M(N) \ge 1$ and let $p_w(N) \in (0, 1]$, $w \in W_N$, be edge probabilities. On a probability space $(\Omega, \mathcal F, \mathbb P)$ let $G_N$, $N \ge 1$, be random bipartite graphs on $V_N \times W_N$ ($|V_N| = N$, $|W_N| = M(N)$) such that, for each $N$, the edges of $G_N$ are present independently, $(v, w)$ with probability $p_w(N)$. Nothing is assumed about the joint law of graphs with different $N$. Write $\bar p(N) = \min_{w \in W_N} p_w(N)$ and $\|p(N)^{-1}\|_2^{-2} = \bigl(\sum_{w \in W_N} p_w(N)^{-2}\bigr)^{-1}$. If
--   $$\bar p(N) = \omega\Bigl(\frac{\ln M(N) + \ln N}{N}\Bigr) \qquad\text{and}\qquad \|p(N)^{-1}\|_2^{-2} = \omega\Bigl(\frac{\ln N}{M(N)^2}\Bigr),$$
--   that is, both ratios tend to $+\infty$, then almost surely the sequence $\{G_N\}_{N \ge 1}$ satisfies the subcriticality condition of Definition 3.3 for JSQ($d$).
--
--   This is the subcriticality half of Theorem 3.6; its hypotheses are conditions (1) and (3) of (3.5).
--
--   **Formalization Note** "$f = \omega(g)$" is $f(N)/g(N) \to \infty$ (§1.4 of the paper). At $N = 1$ a denominator $\ln 1$ can vanish and Lean's $x/0 = 0$ gives a junk term; this affects finitely many $N$ and no limit. Subcriticality is the repaired Definition 3.3 (see the definition item). The paper's proof verifies (A.19) and concludes with the reduction "(A.19) implies subcriticality"; the statement here is the printed conclusion.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 37, Lemma B.2

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_GraphConditions
import Definitions.Def_StrictCompatLB_Inhomogeneous_RandomGraph

open MeasureTheory Filter Topology

namespace StrictCompatLB.Inhomogeneous

/-- Lemma B.2 (p. 37): if `p̄(N) = ω((ln M(N) + ln N)/N)` and
`‖p(N)⁻¹‖₂⁻² = ω(ln N / M(N)²)`, the inhomogeneous random bipartite graphs with edge
probabilities `p_w(N)` almost surely satisfy the subcriticality condition for JSQ(`d`). Only the
law of each `G_N` is prescribed (no assumption on the joint law across `N`). -/
theorem lemma_B2 (d : ℕ) (hd : 2 ≤ d) (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (p : (N : ℕ) → Fin (M N) → ℝ) (hp_pos : ∀ N w, 0 < p N w) (hp_le : ∀ N w, p N w ≤ 1)
    (h_min : Tendsto (fun N : ℕ =>
      minEdgeProb M p N / ((Real.log (M N) + Real.log N) / (N : ℝ))) atTop atTop)
    (h_norm : Tendsto (fun N : ℕ =>
      invNormSq M p N / (Real.log N / (M N : ℝ) ^ 2)) atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (N : ℕ) → Ω → (Fin N × Fin (M N) → Bool))
    (hX_meas : ∀ N, Measurable (X N)) (hX_law : ∀ N, P.map (X N) = edgeLaw M p N) :
    ∀ᵐ ω ∂P, StrictCompatLB.MeanField.IsSubcritical d M (fun N => graphOf (X N ω)) := by sorry

end StrictCompatLB.Inhomogeneous
