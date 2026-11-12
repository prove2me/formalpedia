-- Prove2me | Theorems.Thm_SteurerHDX_theorem_2_3
-- name    : SteurerHDX.theorem_2_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:35:30.637408+00:00
-- url     : https://prove2.me/theorems/3ed1c5a7-ac70-4b81-b439-8a67c81844a9
-- title:
--   Theorem 2.3: local-to-global spectral gap of the down-up walk (corrected: positive part of the base)
-- statement:
--   This is the local-to-global theorem for top-link expanders (Dikstein–Kaufman, Oppenheim, Alev–Lau), as quoted in the paper.
--
--   Let $\mathcal X$ be a pure $d$-dimensional simplicial complex with at least two facets that is **connected** (the 1-skeleton of every link of codimension $\ge2$ is connected), and let $0<\delta<1$. Suppose $\mathcal X$ is a $\frac{1-\delta}{d}$-top-link expander, i.e. $\lambda_2(\tau)\le\frac{1-\delta}{d}$ for every face $\tau$ with $|\tau|=d-2$. Then the down-up walk $P_d^\vee$ satisfies
--   $$1-\lambda_2(P_d^\vee)\ \ge\ \frac{\Bigl(\max\bigl\{0,\ 1-\frac{1-\delta}{\delta d}\bigr\}\Bigr)^{d}}{d},$$
--   and, for $\delta=\tfrac12$,
--   $$1-\lambda_2(P_d^\vee)\ \ge\ \frac{1}{e\cdot d}.$$
--
--   The theorem turns spectral information about the small top links into a spectral gap of the global down-up walk; with $\delta=1/2$ it is the step that gives the sparse expanders of Theorem 2.4 their down-up gap.
--
--   **Formalization Note** $\lambda_2$ is counted with multiplicity. The second clause is stated separately, as printed: it does not follow from the first, since $(1-1/d)^d<1/e$.
--
--   Differences from the source:
--   - correction: spectral gap ≥ (1 − (1−δ)/(δd))^d / d → spectral gap ≥ (max{0, 1 − (1−δ)/(δd)})^d / d; reason: the printed bound is false: d = 2, δ = 1/5, the Petersen graph as a pure 2-dimensional complex is connected with top-link λ₂(∅) = 1/3 ≤ 2/5, but its down-up walk has spectrum {1, 2/3, 1/6, 0} and gap 1/3 < (1 − 2)²/2 = 1/2; where the base is ≥ 0, and for every odd d, the corrected bound is the printed one
--   - reading: connected d-dimensional complex → pure d-dimensional complex (IsPure) that is connected (IsConnectedComplex); reason: λ₂(τ) of Definition 2.2 is undefined for a top link with fewer than two vertices, which is the non-pure case; Theorems 2.4 and 3.1, where the theorem is used, concern pure complexes
--   - reading: δ unrestricted → 0 < δ < 1; reason: δ is the parameter of a (1−δ)/d-top-link expander and only δ = 1/2 is used; outside (0, 1) the bound fails: on the triangle complex (d = 2, top link K₃ with λ₂ = −1/2, down-up gap 3/4) δ = 2 gives 25/32 > 3/4 and δ = −1 gives 2 > 3/4
--   - encoding: no condition on the number of facets → 2 ≤ |X(d)|; reason: λ₂ of a one-state chain is undefined; the condition only excludes that case (and forces d ≥ 1)
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Theorem 2.3, p.4

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_SteurerHDX_IsConnectedComplex
import Definitions.Def_SteurerHDX_IsTopLinkExpander
import Definitions.Def_SteurerHDX_spectralGap
import Definitions.Def_SteurerHDX_downUp

namespace SteurerHDX

/-- **Theorem 2.3 (local-to-global; corrected: positive part of the base).** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292,
Theorem 2.3, p.4 (citing [DK17, Opp18, AL20]): "If X is a connected d-dimensional
(1−δ)/d-top-link spectral expander then the spectral gap of the down-up walk matrix (P_d^∨) is at
least (1 − (1−δ)/(δd))^d / d. In particular, for δ = 1/2, we get a lower bound of 1/(e·d)."

**Formalization Note.**
* Correction: the base is replaced by its positive part, max{0, 1 − (1−δ)/(δd)}. The printed bound
  is false for d = 2, δ = 1/5 on the Petersen graph viewed as a pure 2-dimensional complex (top
  link λ₂ = 1/3 ≤ 2/5, down-up gap 1/3 < 1/2). Where the base is ≥ 0 (and for every odd d) the
  statement is the printed one.
* "connected d-dimensional" is read as pure d-dimensional (`IsPure`), with `IsConnectedComplex`;
  δ ranges over (0, 1); `2 ≤ |X(d)|` makes λ₂ of the down-up walk meaningful (it also forces
  d ≥ 1).
* Clause (b) (δ = 1/2) is stated separately, as printed. -/
theorem theorem_2_3 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ) (δ : ℝ)
    (hX : IsPure X d) (hconn : IsConnectedComplex X d) (hcard : 2 ≤ (faces X d).card)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hexp : IsTopLinkExpander X d ((1 - δ) / d)) :
    (max 0 (1 - (1 - δ) / (δ * d))) ^ d / d ≤ spectralGap (downUp X d) ∧
      (δ = 1 / 2 → 1 / (Real.exp 1 * d) ≤ spectralGap (downUp X d)) := by sorry

end SteurerHDX
