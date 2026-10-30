-- Prove2me | Theorems.Thm_RoboAdvising_Sensitivity_proposition_5_1_ii_corrected
-- name    : RoboAdvising.Sensitivity.proposition_5_1_ii_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:40:54.783965+00:00
-- url     : https://prove2.me/theorems/0f554f77-b906-4fe3-a8cf-19b602fa9585
-- title:
--   Proposition 5.1(ii) and (5.6) (corrected: corner-sensitive derivatives)
-- statement:
--   Let $\sigma_0>0$ be the initial market-return volatility, $s=\sigma_\epsilon>0$ the shock scale, $p=p_\epsilon\in[0,1]$ the shock probability, and $\beta\ge0$ the behavioral-bias coefficient. Assume $\beta+p>0$, and put $a=\beta\sigma_0$. For every real $\phi\ge1$, use the exact proxy
--
--   $$
--   \widetilde{\mathcal R}_P(\phi)=\sqrt{\frac2\pi}\left[\frac a{\sqrt\phi}\left(1-\frac{\phi-1}{2}p\right)+\sqrt{\frac{a^2}{\phi}+s^2}\,\frac{\phi-1}{2}p\right].
--   $$
--
--   An optimum minimizes this function against every real $\psi\ge1$. The complete optimization conclusion is:
--
--   1. If $\beta=0$, the unique optimum is $1$, and the selection $\Phi(P)$ equals $1$.
--   2. If $\beta>0$ and $p>0$, an optimum exists and is unique, and $\phi$ is optimal if and only if $\phi=\Phi(P)$.
--   3. If $p=0$, there is no finite optimum; the objective strictly decreases on $[1,\infty)$ and tends to $0$ at infinity.
--
--   For $\beta,p>0$, the optimizer is globally nondecreasing in each of $\beta,\sigma_0$, and nonincreasing in each of $p,s$, holding the other parameters fixed. Every increase of a parameter stays within its standing range. Each comparison is strict whenever the starting optimizer is greater than $1$, including changes that cross the corner threshold. These are all four comparisons already contained in the published optimizer theorem.
--
--   Write
--
--   $$
--   H=\sqrt{1+\frac{s^2}{\beta^2\sigma_0^2}}-1-\frac1p.
--   $$
--
--   Then $\Phi(P)=1$ if and only if $H\ge0$, and $\Phi(P)>1$ if and only if $H<0$. On the interior branch $H<0$, all four partial derivatives exist and satisfy
--
--   $$
--   \partial_\beta\Phi>0,\qquad\partial_{\sigma_0}\Phi>0,\qquad\partial_p\Phi<0,\qquad\partial_s\Phi<0.
--   $$
--
--   On the open corner branch $H>0$, each one-parameter section is locally constant at $1$ and all four partial derivatives exist and equal zero. The $p$ derivative is within $(0,1]$; at $0<p<1$ it is also an ordinary two-sided derivative. At $H=0$ the optimizer and global comparisons remain asserted, without a differentiability claim. No finite optimizer sensitivity is asserted at $p=0$.
--
--   This composite statement refines the existing single paper mission by supplying actual derivatives, while retaining every optimizer and global-order clause already proved. The new work is the derivative refinement; the published reference alone establishes no derivative existence or sign for $\Phi$.
--
--   **Formalization Note** The selected minimizer is defined from actual minimization, never from the desired sensitivities. For positive $\beta,p$, its relevant neighborhoods stay in the finite-minimizer domain, with the $p=1$ neighborhood taken within the probability range. The original seven clauses are reproduced explicitly; the corresponding Proved item is a reference for a future proof, not an extra premise.
--
--   Differences from the source:
--   - correction: (5.6) asserts four strict derivative signs throughout β>0 and p>0 → strict signs with derivative existence for H<0; local constancy and four zero derivatives for H>0; no derivative assertion at H=0, with optimizer and global comparisons retained; reason: β=σ₀=1, p=1/2, s=4 satisfies all restrictions and has H=√17−3>0 and f′(1)=(√17−3)/4>0; the optimum is identically 1 in a neighborhood, contradicting all printed strict signs
--   - reading: the p=0 branch writes argmin = ∞ alongside the prose existence claim → no attained finite minimizer, strict decrease over all real φ≥1, and limit 0 at infinity; reason: the explicit objective is √(2/π)βσ₀/√φ in this branch; Appendix C p.46 supplies its strict decrease and zero limit
--   - encoding: §5.1 uses integer schedules but Proposition 5.1 differentiates in φ and uses [1,∞) → optimization over the entire unbounded real interval [1,∞); reason: this is the continuous relaxation expressly used in (5.6), without a horizon bound or grid
--   - encoding: p is a probability in [0,1] and (5.6) writes a p derivative → HasDerivWithinAt on (0,1], together with HasDerivAt for 0<p<1; reason: at p=1 the admissible derivative is from the left; no p>1 extension or endpoint exclusion is needed
--   - encoding: φ₀ names the unique finite argmin → Φ is a choice from actual global minimizers, with default 1 only when no minimizer exists; its agreement and uniqueness are conclusions; reason: a total parameterized function is needed to express partial derivatives, and positive parameter neighborhoods avoid its default
--   - encoding: Appendix C uses g(1) to classify the corner and interior regimes → H is written as the existing gAux P 1, with Φ=1 iff H≥0 and Φ>1 iff H<0; reason: at φ=1 the middle term vanishes and g(1)=√(1+s²/(β²σ₀²))−1−1/p exactly
-- source:
--   Capponi, Ólafsson, Zariphopoulou, Personalized Robo-Advising: Enhancing Investment through Client Interaction, arXiv:1911.01391v2, pp.21–22, Proposition 5.1(ii) and (5.6); Appendix C, pp.46–47, proof of Proposition 5.1.

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model
import Definitions.Def_RoboAdvising_Sensitivity_optimizer
open RoboAdvising.Interaction

namespace RoboAdvising.Sensitivity

/-- Proposition 5.1(ii) and (5.6), arXiv:1911.01391v2, pp. 21–22;
Appendix C, pp. 46–47. Corrected only for the corner-sensitive derivatives.
The first seven clauses retain every clause of the published optimizer/order theorem.
The selector is tied to actual minimization in the conclusions, never a hypothesis.
Here gAux P 1 = sqrt(1 + se^2/(β^2 sig0^2)) - 1 - 1/pe.
Strict partial derivatives hold on gAux P 1 < 0; the open corner branch has
locally constant selector and zero partial derivatives. At gAux P 1 = 0 the
optimizer and global comparisons still apply, with no differentiability assertion.
The pe derivative is within (0,1], and is also two-sided when pe < 1.
Counterexample to the printed strict signs: β = sig0 = 1, pe = 1/2, se = 4;
gAux P 1 = sqrt 17 - 3 > 0, so all four derivatives are zero.
No finite optimizer or optimizer derivative is asserted at pe = 0. -/
theorem proposition_5_1_ii_corrected (P : Params) (hS : P.Standing)
    (hpos : 0 < P.β + P.pe) :
    (P.β = 0 → ∀ φ : ℝ, IsOptInteraction P φ ↔ φ = 1) ∧
    (0 < P.β → 0 < P.pe → ∃! φ0 : ℝ, IsOptInteraction P φ0) ∧
    (P.pe = 0 → (∀ φ : ℝ, ¬ IsOptInteraction P φ) ∧
      StrictAntiOn (Rtilde P) (Set.Ici 1) ∧
      Filter.Tendsto (Rtilde P) Filter.atTop (nhds 0)) ∧
    (0 < P.β → 0 < P.pe → ∀ β' φ φ' : ℝ, P.β < β' →
      IsOptInteraction P φ → IsOptInteraction { P with β := β' } φ' →
      φ ≤ φ' ∧ (1 < φ → φ < φ')) ∧
    (0 < P.β → 0 < P.pe → ∀ s' φ φ' : ℝ, P.sig0 < s' →
      IsOptInteraction P φ → IsOptInteraction { P with sig0 := s' } φ' →
      φ ≤ φ' ∧ (1 < φ → φ < φ')) ∧
    (0 < P.β → 0 < P.pe → ∀ p' φ φ' : ℝ, P.pe < p' → p' ≤ 1 →
      IsOptInteraction P φ → IsOptInteraction { P with pe := p' } φ' →
      φ' ≤ φ ∧ (1 < φ → φ' < φ)) ∧
    (0 < P.β → 0 < P.pe → ∀ s' φ φ' : ℝ, P.se < s' →
      IsOptInteraction P φ → IsOptInteraction { P with se := s' } φ' →
      φ' ≤ φ ∧ (1 < φ → φ' < φ)) ∧
    (P.β = 0 → optimizer P = 1) ∧
    (0 < P.β → 0 < P.pe →
      (∀ φ : ℝ, IsOptInteraction P φ ↔ φ = optimizer P) ∧
      (optimizer P = 1 ↔ 0 ≤ gAux P 1) ∧
      (1 < optimizer P ↔ gAux P 1 < 0) ∧
      (gAux P 1 < 0 → ∃ dβ dσ dp ds : ℝ,
        HasDerivAt (fun b : ℝ => optimizer { P with β := b }) dβ P.β ∧
        HasDerivAt (fun v : ℝ => optimizer { P with sig0 := v }) dσ P.sig0 ∧
        HasDerivWithinAt (fun q : ℝ => optimizer { P with pe := q }) dp
          (Set.Ioc 0 1) P.pe ∧
        (P.pe < 1 → HasDerivAt (fun q : ℝ => optimizer { P with pe := q }) dp P.pe) ∧
        HasDerivAt (fun v : ℝ => optimizer { P with se := v }) ds P.se ∧
        0 < dβ ∧ 0 < dσ ∧ dp < 0 ∧ ds < 0) ∧
      (0 < gAux P 1 →
        (∀ᶠ b : ℝ in nhds P.β, optimizer { P with β := b } = 1) ∧
        (∀ᶠ v : ℝ in nhds P.sig0, optimizer { P with sig0 := v } = 1) ∧
        (∀ᶠ q : ℝ in nhdsWithin P.pe (Set.Ioc 0 1), optimizer { P with pe := q } = 1) ∧
        (∀ᶠ v : ℝ in nhds P.se, optimizer { P with se := v } = 1) ∧
        HasDerivAt (fun b : ℝ => optimizer { P with β := b }) 0 P.β ∧
        HasDerivAt (fun v : ℝ => optimizer { P with sig0 := v }) 0 P.sig0 ∧
        HasDerivWithinAt (fun q : ℝ => optimizer { P with pe := q }) 0
          (Set.Ioc 0 1) P.pe ∧
        (P.pe < 1 → HasDerivAt (fun q : ℝ => optimizer { P with pe := q }) 0 P.pe) ∧
        HasDerivAt (fun v : ℝ => optimizer { P with se := v }) 0 P.se)) := by sorry

end RoboAdvising.Sensitivity
