-- Prove2me | Theorems.Thm_RobinsonNSIFT_Implicit_theorem_3_2
-- name    : RobinsonNSIFT.Implicit.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:03:05.887582+00:00
-- url     : https://prove2.me/theorems/c6980389-fb08-44f0-9c24-b97f3ca8b0b5
-- title:
--   Theorem 3.2 — nonsmooth implicit-function theorem: strong approximation by a function with Lipschitzian inverse gives a unique Lipschitzian implicit function
-- statement:
--   This is Robinson's implicit-function theorem for nonsmooth functions.
--
--   Let $X$ be a real Banach space and $Y$, $Z$ real normed linear spaces. Let $x_0 \in X$ and $y_0 \in Y$, let $\Xi$ be a neighborhood of $x_0$ and $H$ a neighborhood of $y_0$. Suppose $F : \Xi \times H \to Z$ satisfies $F(x_0, y_0) = 0$, and $f : \Xi \to Z$ satisfies $f(x_0) = 0$. Assume further that
--
--   1. $f \approx_x F$ at $(x_0, y_0)$, i.e. $f$ strongly approximates $F$ in $x$ (Definition 2.4);
--   2. for each $x \in \Xi$, $F(x, \cdot)$ is Lipschitzian on $H$ with modulus $\varphi \ge 0$;
--   3. $f(\Xi)$ is a neighborhood of the origin in $Z$;
--   4. $\delta(f, \Xi) =: d_0 > 0$, where $\delta(f,\Xi) = \inf\{\|f(x_1) - f(x_2)\| / \|x_1 - x_2\| : x_1 \ne x_2 \in \Xi\}$.
--
--   Then for each $\lambda > d_0^{-1}\varphi$ there exist neighborhoods $U \subseteq \Xi$ of $x_0$ and $V \subseteq H$ of $y_0$, and a function $x : V \to U$, such that
--
--   1. $x(y_0) = x_0$;
--   2. $x(\cdot)$ is Lipschitzian on $V$ with modulus $\lambda$:
--   $$
--   \|x(y_1) - x(y_2)\| \le \lambda \|y_1 - y_2\| \qquad (y_1, y_2 \in V);
--   $$
--   3. for each $y \in V$, $x(y)$ is the unique solution in $U$ of $F(x, y) = 0$.
--
--   The theorem gives the same kind of information as the classical implicit-function theorem, with strong Fréchet differentiability of $F$ in $x$ replaced by strong approximation by a function $f$ whose inverse is Lipschitzian, and with Lipschitz continuity of the implicit function in place of differentiability. No differentiability of $F$ or $f$ is assumed: $f$ may be, for instance, a piecewise linear map.
--
--   **Formalization Note** Hypothesis 4 is stated as $d_0 > 0$ together with $\|f(x_1) - f(x_2)\| \ge d_0\|x_1 - x_2\|$ on $\Xi$ (`ExpansionAtLeast f Ξ d₀`), i.e. $d_0 \le \delta(f, \Xi)$, for every such $d_0$. This is equivalent to the paper's statement: taking $d_0 = \delta(f,\Xi)$ gives it, and conversely for $d_0 \le \delta(f,\Xi)$ every $\lambda > \varphi/d_0$ also exceeds $\varphi/\delta(f,\Xi)$. $F$ and $f$ are total curried functions `F x y` constrained on $\Xi \times H$ only; the paper's implicit requirement that the implicit function live where $F$ is defined is made explicit as $U \subseteq \Xi$, $V \subseteq H$, $x(V) \subseteq U$. Neighborhoods are members of the neighborhood filter (not necessarily open). The moduli $\varphi$ and $\lambda$ are nonnegative reals; $\lambda > \varphi/d_0$ is strict, as in the paper, and universally quantified. Only $X$ is assumed complete; scalars are real.
-- source:
--   Robinson, An Implicit-Function Theorem for a Class of Nonsmooth Functions, Math. Oper. Res. 16(2) (1991), Theorem 3.2, p. 299

import Mathlib
import Definitions.Def_RobinsonNSIFT_Implicit_Basic

open Set Filter Topology Metric
open scoped NNReal

namespace RobinsonNSIFT.Implicit

theorem theorem_3_2 {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (x₀ : X) (y₀ : Y) (Ξ : Set X) (H : Set Y) (hΞ : Ξ ∈ 𝓝 x₀) (hH : H ∈ 𝓝 y₀)
    (F : X → Y → Z) (hF₀ : F x₀ y₀ = 0) (f : X → Z) (hf₀ : f x₀ = 0)
    (ha : StronglyApproxInX f F x₀ y₀)
    (φ : ℝ≥0) (hb : ∀ x ∈ Ξ, LipschitzOnWith φ (F x) H)
    (hc : f '' Ξ ∈ 𝓝 (0 : Z))
    (d₀ : ℝ) (hd₀ : 0 < d₀) (hd : ExpansionAtLeast f Ξ d₀)
    (lam : ℝ≥0) (hlam : (φ : ℝ) / d₀ < lam) :
    ∃ U ∈ 𝓝 x₀, ∃ V ∈ 𝓝 y₀, U ⊆ Ξ ∧ V ⊆ H ∧ ∃ x : Y → X, Set.MapsTo x V U ∧
      x y₀ = x₀ ∧ LipschitzOnWith lam x V ∧
      ∀ y ∈ V, F (x y) y = 0 ∧ ∀ x' ∈ U, F x' y = 0 → x' = x y := by sorry

end RobinsonNSIFT.Implicit
