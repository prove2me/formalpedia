-- Prove2me | Theorems.Thm_SuperstarExcl_Complementors_proposition_3
-- name    : SuperstarExcl.Complementors.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:34.642633+00:00
-- url     : https://prove2.me/theorems/576f2d68-f498-43d1-8387-d515b6a09a91
-- title:
--   Proposition 3 — complementors' total surplus is higher under exclusivity than under non-exclusivity
-- statement:
--   Let $\phi>0$ be the value of the Superstar to consumers. Consider the two regimes:
--
--   1. **exclusivity on platform $1$:** the selected exclusivity outcome $(p_1(t),p_2(t),D(t))_{t\in[0,\phi]}$. This is a continuous path of interior price equilibria of the game with $g=(1,0)$ and Superstar value $t$, starting from equal prices at $t=0$. Its outcome at value $\phi$ gives shares $D(\phi)$ and $1-D(\phi)$;
--   2. **non-exclusivity:** an interior price equilibrium $(q,q,E)$ at equal prices of the game with $g=(1,1)$, so $0<E<1$.
--
--   Then the complementors' total surplus is strictly higher under exclusivity:
--   $$
--   FS\bigl(E,\,1-E\bigr)<FS\bigl(D(\phi),\,1-D(\phi)\bigr),
--   $$
--   where $FS(D_1,D_2)=\int_0^{\gamma D_1}(\gamma D_1-k)\lambda(k)\,dk+\int_0^{\gamma D_2}(\gamma D_2-k)\lambda(k)\,dk$.
--
--   Exclusivity of the Superstar thus benefits the fringe of complementors as a whole: switchers save the cost of a second platform, and new entrants become active on the favoured platform.
--
--   **Formalization Note** Neither $E=\tfrac12$ nor $D(\phi)\neq\tfrac12$ is assumed: both are consequences of the equilibrium analysis (Lemmas 2 and 3). The selection of the exclusive outcome as the end point of a continuous equilibrium path from the symmetric outcome follows the paper's proof of Lemma 3. The paper's informal selection (p. 11) does not pin down a single equilibrium on its own.
-- source:
--   Carroni, Madio & Shekhar, Superstar Exclusivity in Two-Sided Markets, accepted manuscript (hdl:11585/922035), p. 17, Proposition 3 (proof App. A.4, pp. 40–41)

import Mathlib
import Definitions.Def_SuperstarExcl_Complementors_Model
import Definitions.Def_SuperstarExcl_Complementors_Market

namespace SuperstarExcl.Complementors

theorem proposition_3 (M : Model) (ϕ : ℝ) (hϕ : 0 < ϕ) (p₁ p₂ D : ℝ → ℝ)
    (hpath : IsExclusivePath M ϕ p₁ p₂ D)
    (q E : ℝ) (hE : IsEquilibrium M ϕ 1 1 q q E) (hE₀ : 0 < E) (hE₁ : E < 1) :
    FS M E (1 - E) < FS M (D ϕ) (1 - D ϕ) := by sorry

end SuperstarExcl.Complementors
