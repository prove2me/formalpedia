-- Prove2me | Theorems.Thm_RobinsonNSIFT_Implicit_eq_3_1_3_2
-- name    : RobinsonNSIFT.Implicit.eq_3_1_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:02:45.878786+00:00
-- url     : https://prove2.me/theorems/36306287-b01b-4fc5-896d-fe1149852839
-- title:
--   Proof of Theorem 3.2, (3.1)–(3.2) — uniform injectivity and surjectivity of F(·, y)
-- statement:
--   This is the key step of the proof of Theorem 3.2: for every $y$ near $y_0$ the partial map $F(\cdot, y)$ is injective with a Lipschitzian inverse on one fixed closed ball, and maps that ball onto a fixed ball about the origin.
--
--   Let $X$ be a real Banach space and $Y$, $Z$ real normed linear spaces. Let $x_0 \in X$, $y_0 \in Y$, let $\Xi$ be a neighborhood of $x_0$ and $H$ a neighborhood of $y_0$. Let $F : \Xi \times H \to Z$ with $F(x_0, y_0) = 0$ and $f : \Xi \to Z$ with $f(x_0) = 0$, and assume
--
--   1. $f \approx_x F$ at $(x_0, y_0)$ (strong approximation, Definition 2.4);
--   2. for each $x \in \Xi$, $F(x, \cdot)$ is Lipschitzian on $H$ with modulus $\varphi \ge 0$;
--   3. $f(\Xi)$ is a neighborhood of the origin in $Z$;
--   4. $d_0 > 0$ and $\|f(x_1) - f(x_2)\| \ge d_0 \|x_1 - x_2\|$ for all $x_1, x_2 \in \Xi$ (i.e. $d_0 \le \delta(f, \Xi)$).
--
--   Then for every $\varepsilon$ with $0 < \varepsilon < d_0$ there exist $\alpha > 0$, $\kappa > 0$ and a neighborhood $V \subseteq H$ of $y_0$ such that $\Omega := B(x_0, d_0^{-1}\alpha) \subseteq \Xi$ and, for every $y \in V$, with $\theta(y) := (1 - \varepsilon d_0^{-1})\alpha - \|F(x_0, y)\|$,
--   $$
--   \delta(F(\cdot, y), \Omega) \ge d_0 - \varepsilon \quad (3.1), \qquad F(\cdot, y)(\Omega) \supseteq B(0, \theta(y)) \supseteq B(0, \kappa) \quad (3.2).
--   $$
--   (The last inclusion is stated as $\kappa \le \theta(y)$.)
--
--   These two facts give, for each $y \in V$, a unique zero of $F(\cdot, y)$ in $\Omega$, and (3.1) together with hypothesis 2 makes that zero a Lipschitzian function of $y$.
--
--   **Formalization Note** The paper states (3.1)–(3.2) for the particular $\alpha, \kappa, \varepsilon, V$ chosen at the start of its proof of Theorem 3.2 (conditions (1)–(4), p. 299); this item states the existence of such choices for every $\varepsilon \in (0, d_0)$. The second half of the paper's condition (1), $\varphi(d_0 - \varepsilon)^{-1} \le \lambda$, only serves conclusion (ii) of Theorem 3.2 and is not part of this item. The paper uses $\Omega \subseteq \Xi$ implicitly (its $h_y$ is a function on $\Omega$ and $F$ lives on $\Xi \times H$); here it is a conclusion. $\delta(\cdot,\cdot)$ is expressed through lower bounds (`ExpansionAtLeast`), which is equivalent to the paper's formulation (take $d_0 = \delta(f,\Xi)$; conversely every bound stated with a lower bound follows from the one stated with $\delta$). $F$ and $f$ are total curried functions constrained on $\Xi \times H$ only; balls are closed; neighborhoods are members of the neighborhood filter; $\varphi$ is a nonnegative real.
-- source:
--   Robinson, An Implicit-Function Theorem for a Class of Nonsmooth Functions, Math. Oper. Res. 16(2) (1991), proof of Theorem 3.2, choices (1)–(4) on p. 299 and (3.1)–(3.2), p. 300

import Mathlib
import Definitions.Def_RobinsonNSIFT_Implicit_Basic

open Set Filter Topology Metric
open scoped NNReal

namespace RobinsonNSIFT.Implicit

theorem eq_3_1_3_2 {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (x₀ : X) (y₀ : Y) (Ξ : Set X) (H : Set Y) (hΞ : Ξ ∈ 𝓝 x₀) (hH : H ∈ 𝓝 y₀)
    (F : X → Y → Z) (hF₀ : F x₀ y₀ = 0) (f : X → Z) (hf₀ : f x₀ = 0)
    (ha : StronglyApproxInX f F x₀ y₀)
    (φ : ℝ≥0) (hb : ∀ x ∈ Ξ, LipschitzOnWith φ (F x) H)
    (hc : f '' Ξ ∈ 𝓝 (0 : Z))
    (d₀ : ℝ) (hd₀ : 0 < d₀) (hd : ExpansionAtLeast f Ξ d₀) :
    ∀ ε : ℝ, 0 < ε → ε < d₀ → ∃ α > (0 : ℝ), ∃ κ > (0 : ℝ), ∃ V ∈ 𝓝 y₀, V ⊆ H ∧
      closedBall x₀ (α / d₀) ⊆ Ξ ∧
      ∀ y ∈ V, ExpansionAtLeast (fun x => F x y) (closedBall x₀ (α / d₀)) (d₀ - ε) ∧
        closedBall (0 : Z) ((1 - ε / d₀) * α - ‖F x₀ y‖) ⊆
          (fun x => F x y) '' closedBall x₀ (α / d₀) ∧
        κ ≤ (1 - ε / d₀) * α - ‖F x₀ y‖ := by sorry

end RobinsonNSIFT.Implicit
