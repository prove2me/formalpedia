-- Prove2me | Theorems.Thm_PlatformEntry_Protective_proposition1_entry_threshold
-- name    : PlatformEntry.Protective.proposition1_entry_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:17.313887+00:00
-- url     : https://prove2.me/theorems/bf094617-c38b-4184-81c2-38868e5a6053
-- title:
--   Proposition 1, PDF pp. 12–13, 33–34 — the platform gains from entry iff a + e_S > Δ, and Δ > 0
-- statement:
--   Let $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$ satisfy condition (5), and let the entry cost be $K>0$. Let $\Pi^P_{E-N}(A)=-A^2E_N/(4D)-K$ be the platform's second-stage gain from entering when the inferred product value is $A=a+e_S$, and $\Delta=\sqrt{-4KD/E_N}$ the entry threshold, both as given in the proof of Proposition 1. Then $\Delta>0$, and for every $A\ge 0$
--   $$\Pi^P_{E-N}(A)>0\iff A>\Delta .$$
--
--   This is the threshold form of the platform's optimal entry strategy: the platform enters exactly the product spaces whose inferred value exceeds $\Delta$. It is what makes the seller's total profit the piecewise function used in Proposition 3.
--
--   **Formalization Note** The gain is the paper's closed form, not recomputed from the game here. The restriction $A\ge 0$ is added: $a+e_S$ is a product value in the paper, and since the gain is even in $A$ the equivalence fails for $A<-\Delta$. $K>0$ is not stated in the paper but is presupposed by $\Delta=\sqrt{\cdots K\cdots}$ (with $K\le 0$ one gets $\Delta=0$ and the platform always enters). Only the first sentence of Proposition 1 is formalized; its three monotonicity bullets are not.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), PDF pp. 12–13, Proposition 1 (first sentence); closed forms in Online Supplement, Appendix A, proof of Proposition 1, PDF pp. 33–34

import Mathlib
import Definitions.Def_PlatformEntry_Protective_Model

namespace PlatformEntry.Protective

/-- Proposition 1 (first sentence), PDF pp. 12–13, with the closed forms of its proof
(PDF pp. 33–34): under (5), Δ > 0, and for a nonnegative inferred value A = a + e_S the platform
strictly gains from entry iff A > Δ. -/
theorem proposition1_entry_threshold (δ f β K : ℝ) (hbox : PlatformEntry.Regimes.InBox δ f β) (h5 : PlatformEntry.Regimes.cond5 δ f β)
    (hK : 0 < K) :
    0 < Delta δ f β K ∧
      ∀ A : ℝ, 0 ≤ A → (0 < entryGain δ f β K A ↔ Delta δ f β K < A) := by sorry

end PlatformEntry.Protective
