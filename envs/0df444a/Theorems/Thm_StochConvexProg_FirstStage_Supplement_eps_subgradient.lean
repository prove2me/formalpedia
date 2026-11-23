-- Prove2me | Theorems.Thm_StochConvexProg_FirstStage_Supplement_eps_subgradient
-- name    : StochConvexProg.FirstStage.Supplement.eps_subgradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:58:03.512535+00:00
-- url     : https://prove2.me/theorems/90315b05-5cde-41f2-af5e-3f0653dda662
-- title:
--   Proof of Theorem 4 (p. 193) — under Theorem 4's hypotheses, ∂_εφ(0) = −M(ε) for every ε > 0
-- statement:
--   Consider the two-stage stochastic convex program of Rockafellar and Wets under its standing assumptions, with $(S,\Sigma,\sigma)$ a probability space. Let $\varphi(u)=\inf_{x\in X}F(x,u)$ be the perturbation function on $U=\mathbb R^{m_1}\times\mathcal L^\infty_{m_2}$, $g$ the dual objective on $Y=\mathbb R^{m_1}\times\mathcal L^1_{m_2}$, and $M(\varepsilon)=\{y\in Y\mid g(y)\ge\sup\mathbf D-\varepsilon\}$ the set of $\varepsilon$-solutions to the dual $\mathbf D$.
--
--   Suppose the constraint sets $C_1$ and $C_2$ are bounded and $\inf\mathbf P<+\infty$. Then for every $\varepsilon>0$ the $\varepsilon$-subgradient set of $\varphi$ at $0$ coincides with $-M(\varepsilon)$: for every $y\in Y$,
--   $$\Big(\varphi(u)\ge[\varphi(0)-\varepsilon]+\langle u,y\rangle\ \ \text{for all } u\in U\Big)\iff g(-y)\ge\sup\mathbf D-\varepsilon .$$
--
--   This identity is the step that turns the general $\varepsilon$-subdifferential formula for directional derivatives of a closed convex function into Theorem 4, whose right-hand side involves only near-optimal dual solutions.
--
--   **Formalization Note** The hypotheses are those of Theorem 4, in which the paper's sentence occurs. The probability-measure assumption is a typeclass argument.
--
--   Differences from the source:
--   - reading: "∂_εφ(0) coincides with −M(ε)" → for every y ∈ Y, y ∈ ∂_εφ(0) ↔ −y ∈ M(ε); reason: equality of a set with the negated set, written elementwise
--   - reading: the claim sits inside the proof of Theorem 4 → its hypotheses (C₁, C₂ bounded, inf P < +∞, ε > 0) are bound explicitly; reason: the proof assumes the theorem's hypotheses and uses them through Theorem 3 (φ(0) = inf P = sup D finite)
--   - encoding: R ∪ {±∞}, ℒ^∞, ℒ¹ → EReal, Mathlib's Lp ⊤ and Lp 1 (a.e. classes); reason: inherited conventions of the published duality layer, no instance changes
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 193, proof of Theorem 4, second sentence (∂_εφ(0) coincides with −M(ε) by (4.1))

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem
import Definitions.Def_StochConvexProg_Duality_Dual
import Definitions.Def_StochConvexProg_FirstStage_Supplement_EpsSolutions

open MeasureTheory StochConvexProg.Duality

namespace StochConvexProg.FirstStage.Supplement

/-- Rockafellar–Wets (1976), p. 193, proof of Theorem 4: under the hypotheses of Theorem 4
(`C₁`, `C₂` bounded, `inf P < +∞`), for every `ε > 0` the `ε`-subgradient set `∂_εφ(0)` coincides
with `−M(ε)`: `y ∈ ∂_εφ(0)` if and only if `−y` is an `ε`-solution to `D`. -/
theorem eps_subgradient {S : Type*} [MeasurableSpace S] {σ : Measure S}
    [IsProbabilityMeasure σ] {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂)
    (hC₁ : Bornology.IsBounded pr.C₁) (hC₂ : Bornology.IsBounded pr.C₂) (hP : pr.infP < ⊤)
    (ε : ℝ) (hε : 0 < ε) (y : YSpace σ m₁ m₂) :
    y ∈ epsSubdiffZero pr.phi ε ↔ -y ∈ epsSolutions pr ε := by sorry

end StochConvexProg.FirstStage.Supplement
