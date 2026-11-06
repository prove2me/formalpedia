-- Prove2me | Theorems.Thm_RankOneSK_lemma_5_1
-- name    : RankOneSK.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:46.389886+00:00
-- url     : https://prove2.me/theorems/e1acede9-c515-4933-9f7b-422bf3dd42b4
-- title:
--   Lemma 5.1 — moments of $R_X^{n_1}R_Y^{n_2}\varphi(X)^{n_3}\varphi(Y)^{n_4}M^{n_5}$ and its $\bar J$-derivatives are bounded uniformly in $a,b$
-- statement:
--   Let $\mu_{J,a,b}$ be the two-spin Ising measure, $\bar J=\tanh J$, and let $R_X(\bar J,y)$, $R_Y(\bar J,x)$, $M(\bar J,x,y)$ be the quantities of (39) and (51) for this measure, viewed as functions of $\bar J\in(-1,1)$; $\varphi(X)$, $\varphi(Y)$ are the normalized spins. Fix $0\le s\le1$ (the parameter of $M$).
--
--   **Lemma 5.1.** There is an absolute constant $C$ such that for all fields $a,b\in\mathbb R$ and all nonnegative integers $n_{R_X},n_{R_Y},n_X,n_Y,n_M$ with $n_{R_X}+n_X\le2$, $n_{R_Y}+n_Y\le2$, $n_M\le1$, the function
--   $$F(\bar J,x,y)=R_X(\bar J,y)^{n_{R_X}}R_Y(\bar J,x)^{n_{R_Y}}\varphi(X)^{n_X}\varphi(Y)^{n_Y}M(\bar J,x,y)^{n_M}$$
--   satisfies
--   $$\sup_{|\bar J|\le1/2}\mathbb E_{\mu_{0,a,b}}|F|,\quad\sup_{|\bar J|\le1/2}\mathbb E_{\mu_{0,a,b}}\Big|\frac{\partial F}{\partial\bar J}\Big|,\quad\sup_{|\bar J|\le1/2}\mathbb E_{\mu_{0,a,b}}\Big|\frac{\partial^2F}{\partial\bar J^2}\Big|\ \le\ C.$$
--
--   This verifies hypothesis (15) of the Master Lemma 2.6 for every product that appears in Lemma 4.2. The content is uniformity in $a,b$: $\varphi$ is unbounded as $|a|\to\infty$, so no pointwise bound holds.
--
--   Differences from the source:
--   - reading: standing assumption of §5 (p.28): 0 ⩽ s ⩽ 1 → 0 ⩽ s ⩽ 1 as a hypothesis, with C chosen before s; reason: the section states it once at its top; "absolute constant" means C does not depend on s
--   - encoding: R_X(J̄, y), R_Y(J̄, x), M(J̄, x, y) as functions of J̄ → resX, resY, rankOneM at J = artanh J̄; derivatives as deriv in J̄; reason: tanh is a bijection onto (−1, 1)
--   - encoding: sup over |J̄| ⩽ 1/2 of each expectation is ⩽ C → each expectation is ⩽ C for every |J̄| ⩽ 1/2; reason: equivalent
--   - encoding: x, y ∈ {±1}; expectations under µ_{J,a,b} → Bool spins read as ±1; twoSpinExp J a b; reason: Lean convention; same objects
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Lemma 5.1, p.29 (PDF p.30); standing assumption 0 ⩽ s ⩽ 1, p.28

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_twoSpinExp
import Definitions.Def_RankOneSK_resX
import Definitions.Def_RankOneSK_resY
import Definitions.Def_RankOneSK_phi
import Definitions.Def_RankOneSK_rankOneM

open OAI.SKGap MeasureTheory ProbabilityTheory Filter

namespace RankOneSK

/-- **Lemma 5.1.** Let `F(J̄, x, y) = R_X(J̄, y)^{n_RX} R_Y(J̄, x)^{n_RY} φ(X)^{n_X} φ(Y)^{n_Y} M(J̄, x, y)^{n_M}` with
nonnegative integers `n_RX + n_X ⩽ 2`, `n_RY + n_Y ⩽ 2`, `n_M ⩽ 1`. Then there is an absolute constant `C`,
independent of `a, b`, such that `sup_{|J̄|⩽1/2} E_{µ_{0,a,b}}|F|`, `sup_{|J̄|⩽1/2} E_{µ_{0,a,b}}|∂F/∂J̄|`,
`sup_{|J̄|⩽1/2} E_{µ_{0,a,b}}|∂²F/∂J̄²| ⩽ C`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Lemma 5.1, p.29; standing assumption `0 ⩽ s ⩽ 1` of §5, p.28.

**Formalization Note** Two-spin objects: spins are `Bool` read as ±1 by `spinValue`; `twoSpinExp J a b` is
`E_{µ_{J,a,b}}` and `twoSpinExp 0 a b` is `E_{µ_{0,a,b}}`. `R_X(J̄, y)`, `R_Y(J̄, x)`, `M(J̄, x, y)` are the objects of
(39) and (51) for the measure `µ_{J,a,b}` with `J̄ = tanh J`, i.e. `J = artanh J̄`; the derivatives are
`deriv` in `J̄`. `φ(X) = phi a x`, `φ(Y) = phi b y`. `C` is chosen before `s, a, b`, the exponents and `J̄`;
"sup ⩽ C" is "⩽ C for every `|J̄| ⩽ 1/2`". -/
theorem lemma_5_1 :
    ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ a b : ℝ, ∀ nRX nRY nX nY nM : ℕ,
      nRX + nX ≤ 2 → nRY + nY ≤ 2 → nM ≤ 1 →
      ∀ Jb : ℝ, |Jb| ≤ 1 / 2 →
        let F : ℝ → Bool → Bool → ℝ := fun t x y =>
          resX (Real.artanh t) a b x y ^ nRX * resY (Real.artanh t) a b x y ^ nRY *
            phi a x ^ nX * phi b y ^ nY * rankOneM (Real.artanh t) a b s x y ^ nM
        twoSpinExp 0 a b (fun x y => |F Jb x y|) ≤ C ∧
          twoSpinExp 0 a b (fun x y => |deriv (fun t => F t x y) Jb|) ≤ C ∧
          twoSpinExp 0 a b (fun x y => |deriv (deriv fun t => F t x y) Jb|) ≤ C := by sorry

end RankOneSK
