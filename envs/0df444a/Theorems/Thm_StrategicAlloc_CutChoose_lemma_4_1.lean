-- Prove2me | Theorems.Thm_StrategicAlloc_CutChoose_lemma_4_1
-- name    : StrategicAlloc.CutChoose.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:36:39.273892+00:00
-- url     : https://prove2.me/theorems/be02c85d-bfb9-4717-b58b-e22aca587e0c
-- title:
--   Lemma 4.1 — agent 1 can force Mod-Cut&Choose to cut any given partition of M
-- statement:
--   Let $(X_1,X_2)$ be a partition of the set $M$ of $m$ goods: $X_1\cap X_2=\emptyset$ and $X_1\cup X_2=M$. Then agent 1 has a bid vector $\mathbf b_1\in\mathbb R^m_{\ge 0}$ such that lines 1–5 of Mod-Cut&Choose (the cut phase, which depends only on $\mathbf b_1$) construct bundles $E_1,E_2$ with
--   $$\{E_1,E_2\}=\{X_1,X_2\},$$
--   that is, $(E_1,E_2)=(X_1,X_2)$ or $(E_1,E_2)=(X_2,X_1)$.
--
--   Agent 1 can thus realise any partition of the goods as the cut, up to the order of the two sets. This is the key step towards Corollary 4.2 and the existence of an equilibrium in Theorem 4.3.
--
--   **Formalization Note** `cut c` is the pair $(E_1,E_2)$ after line 5 when agent 1 bids $c$; the goods are sorted by agent 1's bid (see the Mod-Cut&Choose definition). The bid must be non-negative, as Definition 2.7's strategy space requires.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 17, Lemma 4.1

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_StrategicAlloc_CutChoose_Setting
import Definitions.Def_StrategicAlloc_CutChoose_ModCutChoose

namespace StrategicAlloc.CutChoose

/-- Lemma 4.1 (p. 17): for every partition `(X_1, X_2)` of `M`, agent 1 has a non-negative bid
vector under which lines 3–5 of Mod-Cut&Choose construct `{E_1, E_2} = {X_1, X_2}`. -/
theorem lemma_4_1 {m : ℕ} (X₁ X₂ : Finset (Fin m)) (hdisj : Disjoint X₁ X₂)
    (hcover : X₁ ∪ X₂ = Finset.univ) :
    ∃ c : Fin m → ℝ, (∀ g, 0 ≤ c g) ∧ (cut c = (X₁, X₂) ∨ cut c = (X₂, X₁)) := by sorry

end StrategicAlloc.CutChoose
