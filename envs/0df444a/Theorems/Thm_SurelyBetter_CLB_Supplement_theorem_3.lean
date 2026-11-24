-- Prove2me | Theorems.Thm_SurelyBetter_CLB_Supplement_theorem_3
-- name    : SurelyBetter.CLB.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:49:56.673213+00:00
-- url     : https://prove2.me/theorems/53bc9c27-03cb-43a7-9081-80137ee34700
-- title:
--   Theorem 3, p. 7629 — smooth ambiguity preferences with −φ″(a)/φ′(a) ≤ 1/a for all a > 0 satisfy monotonicity in optimal mixtures
-- statement:
--   Let $S$ be a finite set of states, $\Delta(S)$ the set of probability measures on $S$, and suppose $u(X)=[0,\infty)$ (the standing assumption of §6.2), so that acts are represented by utility profiles $v:S\to[0,\infty)$. Consider the smooth ambiguity preference (5)
--   $$V_{\phi,\mu}(v)=\int_{\Delta(S)}\phi\Big(\sum_{s}v(s)p(s)\Big)\,d\mu(p),$$
--   where $\mu$ is any (countably additive) probability measure on $\Delta(S)$ and $\phi:[0,\infty)\to\mathbb R$ satisfies:
--
--   1. $\phi$ is continuous and strictly increasing on $[0,\infty)$;
--   2. $\phi$ is twice continuously differentiable on $(0,\infty)$ with $\phi'>0$ and $\phi''\le0$ there;
--   3. $\phi$ is everywhere at most as concave as the natural logarithm:
--   $$-\frac{\phi''(a)}{\phi'(a)}\le\frac1a\qquad\text{for all } a>0.$$
--
--   Then the preference satisfies monotonicity in optimal mixtures (Definition 2) over all acts: for all profiles $f,f',g$ with values in $[0,\infty)$ and $f\le f'$ statewise, the set of optimal mixture weights of $f$ against $g$ is smaller in the set order than that of $f'$ against $g$.
--
--   Together with Theorem 4, this shows that the natural-log bound on the coefficient of ambiguity aversion is the exact frontier for monotonicity in optimal mixtures among smooth ambiguity preferences: ambiguity aversion is compatible with the condition as long as it is not too strong.
--
--   **Formalization Note** $\Delta(S)$ is `stdSimplex ℝ S` with its Borel $\sigma$-algebra and $\mu$ a probability measure on it. $\phi'$ and $\phi''$ are `deriv φ` and `deriv (deriv φ)`, used only at points $a>0$, where $\phi$ is $C^2$; $\phi$ is only required to be continuous at $0$. Hypothesis 1 is part of the model (5); strict monotonicity also follows from continuity at $0$ and $\phi'>0$.
--
--   Differences from the source:
--   - encoding: acts and u(X) = [0,∞) → utility profiles S → ℝ with values in [0,∞); reason: the standing assumption of §6.2 (p. 7629); within the model preferences depend only on utility profiles
--   - encoding: "μ is a countably additive probability measure over probability measures over states S" → a probability measure on stdSimplex ℝ S with its Borel σ-algebra; reason: Δ(S) of a finite S is the standard simplex; same instances
-- source:
--   Ghili & Klibanoff, If It Is Surely Better, Do It More? Implications for Preferences Under Ambiguity, Management Science 67(12) (2021), p. 7629, Theorem 3 (model (5), p. 7622; standing assumption of §6.2, p. 7629)

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model
import Definitions.Def_SurelyBetter_CLB_Supplement_Smooth

namespace SurelyBetter.CLB.Supplement
open SurelyBetter.CLB MeasureTheory
theorem theorem_3 {S : Type*} [Fintype S] (φ : ℝ → ℝ)
    (hφ_cont : ContinuousOn φ (Set.Ici 0)) (hφ_mono : StrictMonoOn φ (Set.Ici 0))
    (hφ_C2 : ContDiffOn ℝ 2 φ (Set.Ioi 0))
    (hφ'_pos : ∀ a : ℝ, 0 < a → 0 < deriv φ a)
    (hφ''_nonpos : ∀ a : ℝ, 0 < a → deriv (deriv φ) a ≤ 0)
    (hlog : ∀ a : ℝ, 0 < a → -deriv (deriv φ) a / deriv φ a ≤ 1 / a)
    (μ : Measure (stdSimplex ℝ S)) [IsProbabilityMeasure μ] :
    MOMOn (smoothV φ μ) (Profiles (Set.Ici 0)) := by sorry
end SurelyBetter.CLB.Supplement
