-- Prove2me | Theorems.Thm_WFMFG_Conv_theorem_2_4
-- name    : WFMFG.Conv.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:33.605543+00:00
-- url     : https://prove2.me/theorems/cf6d1373-911c-45fe-9488-f5cb73d2632d
-- title:
--   Theorem 2.4, p. 14 — normalized N-player equilibrium values are within $CN^{-\chi}$ (times weight factors) of the master equation solution along $\mu^N_{x,y}$
-- statement:
--   Let $d \ge 1$ and $\gamma' \in (0,1)$. There is an exponent $\chi > 0$ with the following property. For all $\varepsilon \in (0,1)$, $T > 0$ and bounds $M_f, M_g$ there is a threshold $\bar\kappa_0$ such that, for every $\kappa \ge \bar\kappa_0$, $\delta \in (0, 1/(4\sqrt d))$, cutoff $\varphi$ (2.2) with parameters $\kappa,\delta$, costs $f, g : [\![d]\!]\times\mathcal S_{d-1}\to\mathbb R$ with $|f| \le M_f$, $|g| \le M_g$, and every classical solution $U$ of the master equation (2.3) (with $\varepsilon$ in place of $\varepsilon^2$) in the regularity class, there is a constant $C$ such that: for every $N \ge 1$, every bounded classical solution $(w^{N,l})_{l}$ of the normalized Nash system (3.2)–(3.3), every $l \in [\![N]\!]$, $t \in [0,T]$, $x \in [\![d]\!]^N$ and $y \in \mathbb Y$,
--   $$
--   \big|(z^{N,l} - w^{N,l})(t,x,y)\big| \le C N^{-\chi}\Big(\prod_{i\in[\![d]\!]}\frac{1}{N^{-\epsilon} + \mu^N_{x,y}[i]}\Big)^{1/(2d)}\Big(\frac1N\sum_{m\in[\![N]\!]}|y^m|^{\ell}\Big)^{1/2}
--   $$
--   with $\epsilon = 1/8$, $\ell = 3$, and $z^{N,l}(t,x,y) = U^{x^l}(t,\mu^N_{x,y})$.
--
--   This is the paper's main result: the equilibrium values of the $N$-player weighted game with Wright–Fisher common noise, normalized by the weights, converge to the solution of the master equation at a polynomial rate, uniformly on sets where $\mu^N_{x,y}$ stays away from the boundary and the weights have bounded third moments.
--
--   **Formalization Note.** (i) The master equation is taken with $\varepsilon$ and $\varepsilon/2$ in front of the common-noise terms where (2.3) prints $\varepsilon^2$, $\varepsilon^2/2$; the $N$-player common noise rings at rate $\varepsilon N$, and only this reading makes Proposition 4.6 and the theorem hold. (ii) The space $[\mathcal C^{1+\gamma'/2,2+\gamma'}_{\mathrm{WF}}]^d$ of Proposition 2.1 is replaced by an explicit regularity class (continuity on $[0,T]\times\mathcal S_{d-1}$, differentiability along the simplex, $U$ and $\mathfrak dU$ bounded, $\mathfrak dU$ and $\sqrt{p_jp_k}\mathfrak d^2U$ bounded and $\gamma'/2$-Hölder), and the Hölder assumptions on $f, g$ by boundedness; $U$ is given, its existence for $d \ge 2$ being Proposition 2.1. (iii) $\chi$ is chosen after $d$ and $\gamma'$ (the proof's exponents involve $\epsilon/(4d)$), $\bar\kappa_0$ after $d, \varepsilon, T, M_f, M_g$, and $C$ after all model data and $U$, before $N$, $w$ and the point. (iv) $w$ is any bounded classical solution of (3.2)–(3.3); by Proposition 3.1 there is exactly one, and it is the paper's $v^{N,l}/y^l$. (v) The bound is asserted for every $t \in [0,T]$.
-- source:
--   Bayraktar, Cecchin, Cohen & Delarue, Finite State Mean Field Games with Wright–Fisher Common Noise as Limits of N-Player Weighted Games, arXiv:2012.04845v2, p. 14, Theorem 2.4, (2.18)–(2.19)

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting

open Finset

namespace WFMFG.Conv

theorem theorem_2_4 (d : ℕ) [NeZero d] (γ' : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1) :
    ∃ χ : ℝ, 0 < χ ∧
    ∀ (ε T Mf Mg : ℝ), 0 < ε → ε < 1 → 0 < T →
    ∃ κbar : ℝ, ∀ κ : ℝ, κbar ≤ κ →
    ∀ δ : ℝ, 0 < δ → δ < 1 / (4 * Real.sqrt d) →
    ∀ φ : ℝ → ℝ, IsCutoff κ δ φ →
    ∀ f g : Fin d → (Fin d → ℝ) → ℝ,
      (∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), |f i p| ≤ Mf) →
      (∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), |g i p| ≤ Mg) →
    ∀ U : Fin d → ℝ → (Fin d → ℝ) → ℝ, IsMasterSol ε T φ f g U → WFReg γ' T U →
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    ∀ w : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ, IsNashSol N ε T φ f g w →
    ∀ (l : Fin N) (t : ℝ) (x : Fin N → Fin d) (y : Fin N → ℚ), t ∈ Set.Icc 0 T → y ∈ Yset N →
      |zN U l t x y - w l t x y| ≤
        C * (N : ℝ) ^ (-χ)
          * (∏ i, 1 / ((N : ℝ) ^ (-(1 / 8 : ℝ)) + empMeas x y i)) ^ (1 / (2 * (d : ℝ)))
          * ((1 / (N : ℝ)) * ∑ m, |(y m : ℝ)| ^ (3 : ℕ)) ^ (1 / 2 : ℝ) := by sorry

end WFMFG.Conv
