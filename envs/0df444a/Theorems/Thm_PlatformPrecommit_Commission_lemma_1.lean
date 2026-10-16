-- Prove2me | Theorems.Thm_PlatformPrecommit_Commission_lemma_1
-- name    : PlatformPrecommit.Commission.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:07.540824+00:00
-- url     : https://prove2.me/theorems/60e68759-4406-442a-8241-6d0a2a27a8d2
-- title:
--   Lemma 1, p. 10 — the unique positive-profit equilibrium of simultaneous price and wage competition
-- statement:
--   Let $\Omega>0$ and $0\leq\beta,\gamma<1$, and put $D=4-3\beta-3\gamma+2\beta\gamma$. In the game where each platform simultaneously chooses a price and wage, the symmetric profile
--
--   $$p_i=\frac{3-2\beta}{D}\Omega,\qquad w_i=\frac{\Omega}{D}$$
--
--   is a Nash equilibrium in which both platforms earn positive profits. Every Nash equilibrium in which both platforms earn positive profits has these prices and wages, and for each platform has matching quantity and profit
--
--   $$z_i=\frac{1-\beta}{D}\Omega,\qquad \pi_i=\frac{2(1-\beta)^2}{D^2}\Omega^2.$$
--
--   This characterizes the no-commitment outcome used in the comparison with commission precommitment.
--
--   **Formalization Note** The printed “unique equilibrium” is read as unique among positive-profit equilibria. Zero-profit equilibria also exist for some parameters because demand and supply use positive parts. Each platform may deviate jointly in price and wage.
-- source:
--   Hu, Liu, Precommitments in Two-Sided Market Competition, submitted manuscript (SSRN 3734828; TSpace), p. 10, Lemma 1; Online Appendix p. 28, Proof of Lemma 1

import Mathlib
import Definitions.Def_PlatformPrecommit_Commission_Setting

namespace PlatformPrecommit.Commission

/-- Lemma 1, with uniqueness restricted to equilibria in which both firms profit. -/
theorem lemma_1 (M : Model) (hM : M.Standing) :
    let D : ℝ := 4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ
    let pw : PW :=
      (fun _ => (3 - 2 * M.β) / D * M.Ω, fun _ => 1 / D * M.Ω)
    (IsPNE M pw ∧ ∀ i, 0 < profP M pw i) ∧
    (∀ x, IsPNE M x → (∀ i, 0 < profP M x i) → ∀ i,
      x.1 i = (3 - 2 * M.β) / D * M.Ω ∧
      x.2 i = 1 / D * M.Ω ∧
      matchP M x i = (1 - M.β) / D * M.Ω ∧
      profP M x i = 2 * (1 - M.β) ^ 2 / D ^ 2 * M.Ω ^ 2) := by sorry

end PlatformPrecommit.Commission
