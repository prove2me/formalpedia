-- Prove2me | Theorems.Thm_RankOneSK_lemma_2_6
-- name    : RankOneSK.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:59.698395+00:00
-- url     : https://prove2.me/theorems/0921d6cc-bbee-4297-a273-e7b8f13f5036
-- title:
--   Lemma 2.6 — Master Lemma: $\mathbb E_{\mu_{J,a,b}}F(\bar J)$ to first order in $\bar J$ with error $O(C\bar J^2)$
-- statement:
--   Let $\mu_{J,a,b}$ be the two-spin Ising measure and $\bar J=\tanh J$, $\bar X_0=\tanh a$, $\bar Y_0=\tanh b$. Let $F:(-1,1)\times\{\pm1\}^2\to\mathbb R$ be twice differentiable in its first argument, and write $\dot F$, $\ddot F$ for its first and second derivatives in $\bar J$.
--
--   **Lemma 2.6.** There is an absolute constant $K$ with the following property. Let $|\bar J|\le\tfrac12$ and $C>0$, and suppose that for each $(x,y)$ there is $\bar J^*(x,y)$ between $0$ and $\bar J$ with
--   $$F(\bar J,x,y)=F(0,x,y)+\bar J\,\dot F(0,x,y)+\frac{\bar J^2}2\,\ddot F(\bar J^*(x,y),x,y)\tag{14}$$
--   and
--   $$\mathbb E_{\mu_{0,a,b}}|F(0,\cdot)|,\ \ \mathbb E_{\mu_{0,a,b}}|\dot F(0,\cdot)|,\ \ \mathbb E_{\mu_{0,a,b}}|\ddot F(\bar J^*(\cdot),\cdot)|\ \le\ C.\tag{15}$$
--   Then
--   $$\Big|\mathbb E_{\mu_{J,a,b}}[F(\bar J,\cdot)]-\mathbb E_{\mu_{0,a,b}}[F(0,\cdot)]-\bar J\Big(\mathbb E_{\mu_{0,a,b}}[\dot F(0,\cdot)]+\mathbb E_{\mu_{0,a,b}}\big[(XY-\bar X_0\bar Y_0)F(0,\cdot)\big]\Big)\Big|\le K\,C\,\bar J^2 .$$
--
--   The lemma transfers expectations under the interacting two-spin measure to the product measure $\mu_{0,a,b}$ with an error uniform in the fields $a,b$. It is the tool behind every clause of Lemma 4.2.
--
--   Differences from the source:
--   - generalization: (15) assumed for all |J̄| ⩽ 1/2, conclusion for all |J̄| ⩽ 1/2 → (15) and (14) assumed only at the J̄ of the conclusion; reason: a pointwise hypothesis is weaker; applying the Lean statement at each J̄ gives the source statement
--   - reading: J̄*(x, y) between 0 and J̄; "for all x, y" in (15) → J̄*(x, y) in the closed interval between 0 and J̄, one choice of J̄* for all (x, y) satisfying (14) and the bound; reason: the inclusive interval is the weaker hypothesis; the expectations in (15) already range over x, y
--   - encoding: F : (−1, 1) × {±1}² → ℝ twice differentiable, Ḟ, F̈ derivatives in J̄ → F : ℝ → Bool → Bool → ℝ, differentiable with differentiable derivative on (−1, 1), Ḟ, F̈ as deriv; reason: values off (−1, 1) never enter
--   - encoding: µ_{J,a,b} with J̄ = tanh J → µ at J = artanh J̄; reason: tanh is a bijection ℝ → (−1, 1) with inverse artanh
--   - encoding: ± O(C·J̄²) → |difference| ⩽ K·C·J̄² with K absolute, chosen before a, b, F, C, J̄; reason: meaning of O(·) with an absolute constant
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Lemma 2.6, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_twoSpinExp

open OAI.SKGap MeasureTheory ProbabilityTheory Filter

namespace RankOneSK

/-- **Lemma 2.6 (Master Lemma).** Let `F : (−1, 1) × {±1}² → ℝ` be twice differentiable in its first
argument `J̄`, and suppose that `F(J̄, x, y) = F(0, x, y) + J̄ Ḟ(0, x, y) + (J̄²/2) F̈(J̄*(x, y), x, y)` (14) for
some `J̄*(x, y)` between `0` and `J̄`, with
`E_{µ_{0,a,b}}|F(0, ·)|, E_{µ_{0,a,b}}|Ḟ(0, ·)|, E_{µ_{0,a,b}}|F̈(J̄*(·), ·)| ⩽ C` (15). Then for `|J̄| ⩽ 1/2`,
`E_{µ_{J,a,b}}[F(J̄, ·)] = E_{µ_{0,a,b}}[F(0, ·)] + J̄(E_{µ_{0,a,b}}[Ḟ(0, ·)] + E_{µ_{0,a,b}}[(XY − X̄₀Ȳ₀)F(0, ·)]) ± O(C J̄²)`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Lemma 2.6, p.13.

**Formalization Note** Two-spin objects: spins are `Bool` read as ±1 by `spinValue`; `twoSpinExp J a b` is
`E_{µ_{J,a,b}}` and `twoSpinExp 0 a b` is `E_{µ_{0,a,b}}`. `J̄ = tanh J` is the first argument of `F`, so the measure at
`J̄` is `µ_{artanh J̄, a, b}`. `F` is a function `ℝ → Bool → Bool → ℝ` whose values off `(−1, 1)` play no
role; `Ḟ`, `F̈` are `deriv` in the first argument. The O(·) is one absolute constant `K`, chosen before
`a, b, F, C, J̄`. Hypothesis (15) is required at the given `J̄` only, for a choice of `J̄*(x, y)` in the
closed interval between `0` and `J̄` satisfying (14). `X̄₀ = tanh a`, `Ȳ₀ = tanh b`. -/
theorem lemma_2_6 :
    ∃ K : ℝ, ∀ (a b C : ℝ) (F : ℝ → Bool → Bool → ℝ), 0 < C →
      (∀ x y, DifferentiableOn ℝ (fun t => F t x y) (Set.Ioo (-1) 1) ∧
        DifferentiableOn ℝ (deriv fun t => F t x y) (Set.Ioo (-1) 1)) →
      ∀ Jb : ℝ, |Jb| ≤ 1 / 2 →
      (∃ Js : Bool → Bool → ℝ,
        (∀ x y, min 0 Jb ≤ Js x y ∧ Js x y ≤ max 0 Jb ∧
          F Jb x y = F 0 x y + Jb * deriv (fun t => F t x y) 0 +
            Jb ^ 2 / 2 * deriv (deriv fun t => F t x y) (Js x y)) ∧
        twoSpinExp 0 a b (fun x y => |F 0 x y|) ≤ C ∧
        twoSpinExp 0 a b (fun x y => |deriv (fun t => F t x y) 0|) ≤ C ∧
        twoSpinExp 0 a b (fun x y => |deriv (deriv fun t => F t x y) (Js x y)|) ≤ C) →
      |twoSpinExp (Real.artanh Jb) a b (F Jb) -
          (twoSpinExp 0 a b (F 0) +
            Jb * (twoSpinExp 0 a b (fun x y => deriv (fun t => F t x y) 0) +
              twoSpinExp 0 a b (fun x y =>
                (spinValue x * spinValue y - Real.tanh a * Real.tanh b) * F 0 x y)))|
        ≤ K * C * Jb ^ 2 := by sorry

end RankOneSK
