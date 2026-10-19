-- Prove2me | Theorems.Thm_SharingPlatform_WageSchemes_lemma_2
-- name    : SharingPlatform.WageSchemes.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:09.39602+00:00
-- url     : https://prove2.me/theorems/94431902-e907-4061-8ad7-03d3d53248ee
-- title:
--   Lemma 2, p. 11 (PDF 12) — the FCR subgame-perfect equilibrium: α* the unique root of (6) in (ᾱ, 1) (A.4) and price (7)
-- statement:
--   Consider the fixed-commission-rate game: in stage 1 the platforms announce commission rates $\alpha_1, \alpha_2 \in \mathbb R$, in stage 2 they set prices, the wage is $(1-\alpha_i)p_i$, and profit is $\alpha_i p_i \max\{0, \min\{d_i, s_i\}\}$. Assume the standing assumptions. Let $\bar\alpha = 1 - \frac{a(b+c) + k(b+2c)}{am}$ and $f(\alpha) = A\alpha^2 + B\alpha + C$ with
--
--   $$\begin{aligned} A &= m(a+k)(b+c)(2l+m) + am\big(m(b+2l+m) + c(l+m)\big),\\ B &= -(c+m)\big(a(2m(2b+c+2l) + l(2b+c) + 2m^2) + bk(2l+m)\big),\\ C &= (c+m)(am-ck)(2b+c+2l+m).\end{aligned}$$
--
--   Equation (6) reads
--
--   $$\frac{(1-\alpha)[m(b+2l+m) + c(l+m)] + b(2c+m) + c(c+l+m)}{(1-\alpha)m(b+c)(2l+m) + c(2b+c)(l+m)} = \frac{\alpha(a+k)}{ma(1-\alpha) - ck},$$
--
--   and (7) is $p^F(\alpha) = \frac{a+k}{c + m(1-\alpha)}$. Then:
--   1. $f$ has exactly one zero $\alpha^*$ in the open interval $(\bar\alpha, 1)$;
--   2. at that zero $ma(1-\alpha^*) - ck > 0$ and (6) holds, and there is a symmetric, non-trivial subgame-perfect equilibrium whose stage-2 price rules are continuous at $(\alpha^*, \alpha^*)$, in which both platforms announce $\alpha^*$ and charge $p^F(\alpha^*)$;
--   3. conversely, every symmetric, non-trivial subgame-perfect equilibrium whose stage-2 price rules are continuous at the equilibrium pair has commission rate in $(\bar\alpha, 1)$ that is a zero of $f$ (hence equal to $\alpha^*$), satisfies $ma(1-\alpha)-ck > 0$ and (6), and has on-path price $p^F(\alpha)$.
--
--   This characterizes the FCR outcome that Proposition 3 compares with DCR and FW.
--
--   **Formalization Note** Uniqueness of the zero in $(\bar\alpha, 1)$ is stated in the proof (A.4, p. 43): "a unique $\alpha^*$ exists in $(\bar\alpha, 1)$ such that $f(\alpha^*) = 0$, which leads to Equation (6)". Cross-multiplying (6) gives exactly $f(\alpha) = 0$. Continuity of the stage-2 price rules at the equilibrium pair is added. The appendix assumes it, since it differentiates the subgame prices (40) in the stage-1 rates. It is needed: with arbitrary off-path rules, every pricing subgame near the diagonal also has a zero-profit equilibrium (both prices very negative), and with it any deviation can be punished. Commission rates other than $\alpha^*$ then become subgame-perfect outcomes (checked numerically at $a = 15$, $k = 1.5$, $c = 2.5$, $m = 2$, $b = 1.5$, $l = 3$).
-- source:
--   Zhang, Chen, Raghunathan, Two-Sided Platform Competition in a Sharing Economy, SSRN 3555993, p. 11 (PDF 12), Lemma 2, Equations (6)–(7); proof A.4, pp. 40–43 (PDF 41–44), (39), (40), (44)

import Mathlib
import Definitions.Def_SharingPlatform_WageSchemes_Model

namespace SharingPlatform.WageSchemes

theorem lemma_2 (P : Params) (hP : P.Standing) :
    (∃! α : ℝ, α ∈ Set.Ioo (alphaBar P) 1 ∧ fFCR P α = 0) ∧
    (∀ α : ℝ, α ∈ Set.Ioo (alphaBar P) 1 → fFCR P α = 0 →
      0 < P.m * P.a * (1 - α) - P.c * P.k ∧ Eq6 P α ∧
      ∃ e : TwoStage, IsSPE P fcrWage e ∧ e.OnPathContinuous ∧ e.IsSymmetric ∧
        e.Nontrivial P fcrWage ∧ e.x₁ = α ∧ e.P₁ e.x₁ e.x₂ = priceFCR P α) ∧
    (∀ e : TwoStage, IsSPE P fcrWage e → e.OnPathContinuous → e.IsSymmetric →
      e.Nontrivial P fcrWage →
      e.x₁ ∈ Set.Ioo (alphaBar P) 1 ∧ fFCR P e.x₁ = 0 ∧
        0 < P.m * P.a * (1 - e.x₁) - P.c * P.k ∧ Eq6 P e.x₁ ∧
        e.P₁ e.x₁ e.x₂ = priceFCR P e.x₁) := by sorry
end SharingPlatform.WageSchemes
