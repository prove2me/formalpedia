-- Prove2me | Theorems.Thm_SurelyBetter_CLB_Supplement_theorem_4
-- name    : SurelyBetter.CLB.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:50:40.290576+00:00
-- url     : https://prove2.me/theorems/12586583-6854-4475-a442-fff8ebae3a6d
-- title:
--   Theorem 4, p. 7630 (corrected: at least two states) — if −φ″(a)/φ′(a) > 1/a at some a > 0, some μ makes the smooth ambiguity preference violate monotonicity in optimal mixtures
-- statement:
--   Let $S$ be a finite set with **at least two states**, $\Delta(S)$ the probability measures on $S$, and $u(X)=[0,\infty)$, so that acts are represented by utility profiles $v:S\to[0,\infty)$. For a probability measure $\mu$ on $\Delta(S)$ write $V_{\phi,\mu}(v)=\int_{\Delta(S)}\phi\big(\sum_s v(s)p(s)\big)\,d\mu(p)$ for the smooth ambiguity functional (5). Let $\phi$ satisfy:
--
--   1. $\phi$ is continuous and strictly increasing on $[0,\infty)$;
--   2. $\phi$ is twice continuously differentiable on $(0,\infty)$ with $\phi'>0$ and $\phi''\le0$ there;
--   3. $\phi$ is somewhere more concave than the natural logarithm:
--   $$-\frac{\phi''(a)}{\phi'(a)}>\frac1a\qquad\text{for some } a>0.$$
--
--   Then there exists a probability measure $\mu$ on $\Delta(S)$ such that the preference represented by $V_{\phi,\mu}$ violates monotonicity in optimal mixtures (Definition 2) over the acts with utility values in $[0,\infty)$.
--
--   Together with Theorem 3, this shows that the natural-log bound is necessary as well as sufficient when the second-order belief $\mu$ is unrestricted.
--
--   **Formalization Note** $\Delta(S)$ is `stdSimplex ℝ S` with its Borel $\sigma$-algebra; $\phi'$ and $\phi''$ are `deriv φ` and `deriv (deriv φ)` at points $a>0$. The hypothesis that $S$ has at least two states (`Nontrivial S`) is added: with a single state every $\mu$ is the point mass at the unique probability measure, the preference is subjective expected utility, and it satisfies monotonicity in optimal mixtures (§5, p. 7625), so the printed statement is false there. The paper's proof uses an event $E\subset S$ with $p_1(E)=1$ and $p_2(E)=0$, which exists exactly when there are at least two states.
--
--   Differences from the source:
--   - correction: "φ … if −φ″(a)/φ′(a) > 1/a for some a > 0, then there exists a measure μ …" for any finite S → the same with S having at least two states (Nontrivial S); reason: counterexample S = {s}: every μ is the point mass at the unique p, the preference is SEU and satisfies monotonicity in optimal mixtures (§5, p. 7625); the proof on p. 7630 takes E ⊂ S with p₁(E) = 1 and p₂(E) = 0, which needs two states; only the one-state case is excluded
--   - encoding: acts and u(X) = [0,∞) → utility profiles S → ℝ with values in [0,∞); reason: the standing assumption of §6.2 (p. 7629)
--   - encoding: "a measure μ" over probability measures over S → a probability measure on stdSimplex ℝ S with its Borel σ-algebra; reason: (5) requires μ to be a countably additive probability measure; Δ(S) is the standard simplex
-- source:
--   Ghili & Klibanoff, If It Is Surely Better, Do It More? Implications for Preferences Under Ambiguity, Management Science 67(12) (2021), p. 7630, Theorem 4 and its proof (model (5), p. 7622; standing assumption of §6.2, p. 7629)

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model
import Definitions.Def_SurelyBetter_CLB_Supplement_Smooth

namespace SurelyBetter.CLB.Supplement
open SurelyBetter.CLB MeasureTheory
theorem theorem_4 {S : Type*} [Fintype S] [Nontrivial S] (φ : ℝ → ℝ)
    (hφ_cont : ContinuousOn φ (Set.Ici 0)) (hφ_mono : StrictMonoOn φ (Set.Ici 0))
    (hφ_C2 : ContDiffOn ℝ 2 φ (Set.Ioi 0))
    (hφ'_pos : ∀ a : ℝ, 0 < a → 0 < deriv φ a)
    (hφ''_nonpos : ∀ a : ℝ, 0 < a → deriv (deriv φ) a ≤ 0)
    (hconc : ∃ a : ℝ, 0 < a ∧ 1 / a < -deriv (deriv φ) a / deriv φ a) :
    ∃ μ : Measure (stdSimplex ℝ S), IsProbabilityMeasure μ ∧
      ¬ MOMOn (smoothV φ μ) (Profiles (Set.Ici 0)) := by sorry
end SurelyBetter.CLB.Supplement
