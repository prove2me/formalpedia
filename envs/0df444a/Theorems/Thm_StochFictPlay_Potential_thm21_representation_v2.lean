-- Prove2me | Theorems.Thm_StochFictPlay_Potential_thm21_representation_v2
-- name    : StochFictPlay.Potential.thm21_representation_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:23.181889+00:00
-- url     : https://prove2.me/theorems/c44507c9-b6c2-4251-9475-27bb603a299a
-- title:
--   Theorem 2.1 — every additive random utility choice function with a continuous strictly positive shock density has an admissible deterministic perturbation representation
-- statement:
--   Let $m \ge 1$ and let $\varepsilon$ be a random vector in $\mathbb R^m$ admitting a strictly positive density $f$ — in the regular sense of the conditions of Theorem 2.1: $f$ is a continuous, finite, everywhere strictly positive probability density — such that the choice function
--   $$C_i(\pi) = P\big(\operatorname*{arg\,max}_j\ \pi_j + \varepsilon_j = i\big)$$
--   is continuously differentiable. Then there is an admissible deterministic perturbation $V : \operatorname{int}(\Delta) \to \mathbb R$ ($C^2$, with $D^2V(y)$ positive definite on the tangent space $\mathbb R^m_0$ and $\|\nabla V(y)\| \to \infty$ as $y$ approaches the boundary of $\Delta$) such that for every payoff vector $\pi \in \mathbb R^m$,
--   $$C(\pi) = \operatorname*{arg\,max}_{y \in \operatorname{int}(\Delta)} \big(y\cdot\pi - V(y)\big),$$
--   the maximizer being unique.
--
--   In this mission the theorem is the bridge from the stochastically perturbed dynamic (P) to the deterministically perturbed dynamic (PV): with $\tilde C^\alpha = C^\alpha$, the fields of (P) and (PV) coincide, so Propositions 4.1–4.3 apply to (P).
--
--   **Formalization Note.** The retired version imported a definition of "strictly positive density" that asked only for pointwise positivity of one measurable representative; since $C$ depends only on the law of $\varepsilon$, a density with a genuine zero could be patched on a null set to pass it, giving a smooth $C$ with a critical point for which no admissible $V$ exists. The new statement is textually the same theorem over the corrected definition module, in which the density is a continuous, finite, strictly positive representative (the version the paper's eq. (4) integrates over hyperplanes; the standard convention of the random-utility literature, under which the density of every payoff difference is positive and the off-diagonal entries of $DC$ are strictly negative). Standing conventions made explicit: $m \ge 1$ (the simplex on $0$ alternatives is empty); one $V$ serves all $\pi$; the argmax is expressed as "$C(\pi)$ lies in $\operatorname{int}(\Delta)$ and strictly beats every other interior point"; admissibility includes $C^2$ regularity of $V$ on $\operatorname{int}(\Delta)$, which is presupposed by "$D^2V$ positive definite" and is what the paper's proof delivers (the inverse of the $C^1$ map $C|_{\mathbb R^m_0}$ with invertible derivative is $C^1$). No correction to the printed source other than reading its density hypothesis in the regular sense.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 5, Theorem 2.1 (hypothesis read with the regularity of the density its proof uses in eq. (4), p. 6)

import Mathlib
import Definitions.Def_StochFictPlay_Potential_ChoiceModel_v2

open MeasureTheory
open scoped ENNReal

namespace StochFictPlay.Potential

/-- Theorem 2.1 (Hofbauer–Sandholm 2002, manuscript p. 5), restated for this mission: if the
shock vector has a strictly positive density `f` on `ℝ^m` — in the regular sense of
`IsRegularDensity`: a continuous, everywhere finite, strictly positive probability density, the
version the proof's eq. (4) integrates over hyperplanes — and the choice function
`C = choiceProb f` is continuously differentiable, there is one admissible deterministic
perturbation `V` (independent of `π`) with `C(π) = argmax_{y ∈ int(∆A)} (y · π − V(y))` for
every `π`, the argmax being unique.

Corrected version of `thm21_representation`, which imported a definition of `IsRegularDensity`
that asked only for pointwise positivity of one measurable version of the density; a density
with a zero was patched on a null set to pass it, giving a choice function with a critical point,
for which no admissible `V` exists. The statement itself is unchanged; the fix is in the
imported definition module. -/
theorem thm21_representation_v2 (m : ℕ) (hm : 1 ≤ m) (f : (Fin m → ℝ) → ℝ≥0∞)
    (hf : IsRegularDensity f) :
    ∃ V : (Fin m → ℝ) → ℝ, IsAdmissible V ∧ IsPerturbedArgmax V (choiceProb f) := by sorry

end StochFictPlay.Potential
