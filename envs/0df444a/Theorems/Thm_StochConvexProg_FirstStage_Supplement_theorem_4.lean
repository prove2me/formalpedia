-- Prove2me | Theorems.Thm_StochConvexProg_FirstStage_Supplement_theorem_4
-- name    : StochConvexProg.FirstStage.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:59:54.340818+00:00
-- url     : https://prove2.me/theorems/9cd83c67-ec9b-4451-8cda-ac881c83d675
-- title:
--   Theorem 4 — with C₁, C₂ bounded and inf P < +∞, φ′(0; u) = lim_{ε↓0} sup_{y∈M(ε)} ⟨u, −y⟩ for every u ∈ U
-- statement:
--   Consider the two-stage stochastic convex program of Rockafellar and Wets under its standing assumptions, with $(S,\Sigma,\sigma)$ a probability space. Let $\varphi(u)=\inf_{x\in X}F(x,u)$ be the perturbation function on $U=\mathbb R^{m_1}\times\mathcal L^\infty_{m_2}$, paired with $Y=\mathbb R^{m_1}\times\mathcal L^1_{m_2}$ by $\langle u,y\rangle=u_1\cdot y_1+\int_S u_2(s)\cdot y_2(s)\,\sigma(ds)$. For $\varepsilon>0$ let $M(\varepsilon)=\{y\in Y\mid g(y)\ge\sup\mathbf D-\varepsilon\}$ be the set of $\varepsilon$-solutions to the dual problem $\mathbf D$.
--
--   Suppose the sets $C_1$ and $C_2$ are bounded and $\inf\mathbf P<+\infty$. Then for every $u\in U$ the one-sided directional derivative
--   $$\varphi'(0;u)=\lim_{\lambda\downarrow 0}\frac{\varphi(\lambda u)-\varphi(0)}{\lambda}$$
--   exists in $[-\infty,+\infty]$, the limit on the right below exists in $[-\infty,+\infty]$, and
--   $$\varphi'(0;u)=\lim_{\varepsilon\downarrow 0}\ \sup_{y\in M(\varepsilon)}\langle u,-y\rangle .$$
--
--   The theorem characterizes the marginal effect of a perturbation $u$ of the constraints on the optimal value of the stochastic program through near-optimal dual solutions only; it holds whether or not the dual problem attains its supremum. The derivative may equal $+\infty$ (in a direction leaving the effective domain of $\varphi$) or $-\infty$.
--
--   **Formalization Note** The statement asserts that there is a $d\in[-\infty,+\infty]$ to which both the difference quotient (as $\lambda\to0^+$) and $\varepsilon\mapsto\sup_{y\in M(\varepsilon)}\langle u,-y\rangle$ (as $\varepsilon\to0^+$) converge; no `lim` junk value is used. The difference quotient is $\lambda^{-1}\cdot(\varphi(\lambda u)-\varphi(0))$ in `EReal` with $\lambda>0$ real, so $\varphi(\lambda u)=+\infty$ gives $+\infty$.
--
--   Differences from the source:
--   - encoding: "φ′(0; u) = lim_{ε↓0} sup_{y∈M(ε)} ⟨u, −y⟩" with φ′(0; u) = lim_{λ↓0} {φ(λu) − φ(0)}/λ → ∃ d : EReal, both functions tend to d along 𝓝[>] 0; reason: the paper notes the derivative exists by convexity and asserts the equation of the two limits; "both limits exist and are equal" is that assertion without a junk value
--   - encoding: {φ(λu) − φ(0)}/λ in R ∪ {±∞} → ((λ⁻¹ : ℝ) : EReal) * (φ(λ • u) − φ(0)); reason: division by a positive real, written as multiplication by its inverse in EReal
--   - encoding: R ∪ {±∞}, ℒ^∞, ℒ¹ → EReal, Mathlib's Lp ⊤ and Lp 1 (a.e. classes); reason: inherited conventions of the published duality layer, no instance changes
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 192, Theorem 4 (directional derivative defined on p. 192 above it)

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem
import Definitions.Def_StochConvexProg_Duality_Dual
import Definitions.Def_StochConvexProg_FirstStage_Supplement_EpsSolutions

open MeasureTheory Filter Topology StochConvexProg.Duality

namespace StochConvexProg.FirstStage.Supplement

/-- Rockafellar–Wets (1976), p. 192, Theorem 4: if `C₁` and `C₂` are bounded and `inf P < +∞`,
then for every `u ∈ U` the directional derivative
`φ′(0; u) = lim_{λ↓0} {φ(λu) − φ(0)}/λ` exists in `[−∞, +∞]` and
`φ′(0; u) = lim_{ε↓0} sup_{y ∈ M(ε)} ⟨u, −y⟩`, where `M(ε)` is the set of `ε`-solutions to `D`.
Both one-sided limits exist and are equal. -/
theorem theorem_4 {S : Type*} [MeasurableSpace S] {σ : Measure S}
    [IsProbabilityMeasure σ] {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂)
    (hC₁ : Bornology.IsBounded pr.C₁) (hC₂ : Bornology.IsBounded pr.C₂) (hP : pr.infP < ⊤)
    (u : USpace σ m₁ m₂) :
    ∃ d : EReal,
      Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * (pr.phi (t • u) - pr.phi 0))
        (𝓝[>] (0 : ℝ)) (𝓝 d) ∧
      Tendsto (fun ε : ℝ => ⨆ y ∈ epsSolutions pr ε, ((pairUY u (-y) : ℝ) : EReal))
        (𝓝[>] (0 : ℝ)) (𝓝 d) := by sorry

end StochConvexProg.FirstStage.Supplement
