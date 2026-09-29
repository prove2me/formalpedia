-- Prove2me | Theorems.Thm_SocialEquilibrium_Existence_exists_saddle_point
-- name    : SocialEquilibrium.Existence.exists_saddle_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:47:00.594715+00:00
-- url     : https://prove2.me/theorems/6a38ae9f-6120-4265-b02c-5d89e70675aa
-- title:
--   COROLLARY — saddle points exist when the argmin and argmax sets are contractible
-- statement:
--   Let $X$ and $Y$ be contractible polyhedra in finite-dimensional real normed spaces (the paper's $\mathbb R^l$ and $\mathbb R^m$), and let $f:X\times Y\to\overline{\mathbb R}$ be continuous into the completed real line. Suppose that for every $x^0\in X$ the set
--   $$U_{x^0}=\{y\in Y\mid f(x^0,y)=\min_{y\in Y}f(x^0,y)\}$$
--   is contractible, and for every $y^0\in Y$ the set
--   $$V_{y^0}=\{x\in X\mid f(x,y^0)=\max_{x\in X}f(x,y^0)\}$$
--   is contractible. Then $f$ has a **saddle point** $(x^0,y^0)$:
--   $$\min_{y}f(x^0,y)=f(x^0,y^0)=\max_x f(x,y^0).$$
--
--   Debreu derives this from the THEOREM and the Remark, applied to two agents with payoffs $f$ and $-f$. It contains the saddle-point theorems of Kakutani and of von Neumann.
--
--   **Formalization Note** The minimum and maximum in $U_{x^0}$ and $V_{y^0}$ are written as `⨅`/`⨆` in `EReal`; they are attained because $X,Y$ are compact and $f$ is continuous. The saddle-point conclusion is stated as $f(x^0,y^0)\le f(x^0,y)$ for all $y$ and $f(x,y^0)\le f(x^0,y^0)$ for all $x$, which is the same as display (1).
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 890, §3 Saddle Points and MinMax Operator, COROLLARY (with display (1))

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron
import Definitions.Def_SocialEquilibrium_Existence_IsContractible

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §3, p. 890, COROLLARY: let `X ⊆ ℝˡ`, `Y ⊆ ℝᵐ` be contractible polyhedra and
`f` a continuous function from `X × Y` to the completed real line. If for every `x⁰ ∈ X` the set
`U_{x⁰} = {y ∈ Y | f(x⁰, y) = Min_{y ∈ Y} f(x⁰, y)}` is contractible and for every `y⁰ ∈ Y` the
set `V_{y⁰} = {x ∈ X | f(x, y⁰) = Max_{x ∈ X} f(x, y⁰)}` is contractible, then `f` has a saddle
point `(x⁰, y⁰)`: `Min_y f(x⁰, y) = f(x⁰, y⁰) = Max_x f(x, y⁰)`. -/
theorem exists_saddle_point {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (X : Set E) (Y : Set F)
    (hX : IsPolyhedron X ∧ IsContractible X) (hY : IsPolyhedron Y ∧ IsContractible Y)
    (f : X × Y → EReal) (hf : Continuous f)
    (hU : ∀ x₀ : X, IsContractible {y : Y | f (x₀, y) = ⨅ y' : Y, f (x₀, y')})
    (hV : ∀ y₀ : Y, IsContractible {x : X | f (x, y₀) = ⨆ x' : X, f (x', y₀)}) :
    ∃ (x₀ : X) (y₀ : Y),
      (∀ y : Y, f (x₀, y₀) ≤ f (x₀, y)) ∧ (∀ x : X, f (x, y₀) ≤ f (x₀, y₀)) := by sorry

end SocialEquilibrium.Existence
