-- Prove2me | Theorems.Thm_SuperstarExcl_Complementors_lemma_3
-- name    : SuperstarExcl.Complementors.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:11.308369+00:00
-- url     : https://prove2.me/theorems/9ecccba1-109e-4df7-9116-e41823d2b164
-- title:
--   Lemma 3 (demand and complementor ranking) — under exclusivity D₁⋆(1,0) > D₂⋆(0,1) and N₁⋆(1,0) > N₂⋆(0,1)
-- statement:
--   Let $\phi>0$, with the Superstar exclusive on platform $1$, $g=(1,0)$. Let $t\mapsto(p_1(t),p_2(t),D(t))$, $t\in[0,\phi]$, be the selected exclusivity outcome: a continuous path of interior price equilibria of the game in which the Superstar is worth $t$, starting from equal prices at $t=0$. Write $D^\star_1=D(\phi)$ and $D^\star_2=1-D(\phi)$. Then
--   $$
--   D^\star_1>D^\star_2\qquad\text{and}\qquad \Lambda(\gamma D^\star_1)>\Lambda(\gamma D^\star_2).
--   $$
--   The platform hosting the Superstar attracts a larger mass of consumers and of complementors than its rival.
--
--   This is the demand effect of exclusivity, on which the welfare results of the paper rest.
--
--   **Formalization Note** The paper's Lemma 3 also ranks prices, $p^\star_1(1,0)>p^\star_1(1,1)=p^\star_2(1,1)>p^\star_2(0,1)$. That part is not stated here: its proof signs price derivatives through bounds on $f'$ that the paper never pins down. The path is the outcome the paper's proof follows when it differentiates in $\phi$ from the symmetric outcome at $\phi=0$.
-- source:
--   Carroni, Madio & Shekhar, Superstar Exclusivity in Two-Sided Markets, accepted manuscript (hdl:11585/922035), p. 13, Lemma 3, demand and complementor part (proof App. A.3, pp. 37–40)

import Mathlib
import Definitions.Def_SuperstarExcl_Complementors_Model
import Definitions.Def_SuperstarExcl_Complementors_Market

namespace SuperstarExcl.Complementors

theorem lemma_3 (M : Model) (ϕ : ℝ) (hϕ : 0 < ϕ) (p₁ p₂ D : ℝ → ℝ)
    (hpath : IsExclusivePath M ϕ p₁ p₂ D) :
    1 - D ϕ < D ϕ ∧ M.Λ (M.γ * (1 - D ϕ)) < M.Λ (M.γ * D ϕ) := by sorry

end SuperstarExcl.Complementors
