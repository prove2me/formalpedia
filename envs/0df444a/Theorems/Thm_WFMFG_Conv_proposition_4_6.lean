-- Prove2me | Theorems.Thm_WFMFG_Conv_proposition_4_6
-- name    : WFMFG.Conv.proposition_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:23.468174+00:00
-- url     : https://prove2.me/theorems/5516a5ce-c236-48df-a2d6-a574461bae7e
-- title:
--   Proposition 4.6 and Remark 4.7, p. 24 — $z^{N,l}$ solves the normalized Nash system (3.2) up to a rest $|r^{N,l}| \le C/N^\eta$ on $\mathcal T_N$
-- statement:
--   Let $\gamma' \in (0,1)$ and $\epsilon \in (0,\frac14)$. There is $\eta > 0$, depending only on $\gamma'$ and $\epsilon$, with the following property. Let $d \ge 1$, $\varepsilon \in (0,1)$, $T > 0$, $\delta > 0$, $\varphi$ a cutoff (2.2) with parameters $\kappa,\delta$, $f, g : [\![d]\!]\times\mathcal S_{d-1} \to \mathbb R$, and let $U$ be a classical solution of the master equation (2.3) (with $\varepsilon$ in place of $\varepsilon^2$) in the regularity class. Then there is $C$ such that for every $N \ge 1$, with $z^{N,l}(t,x,y) = U^{x^l}(t,\mu^N_{x,y})$:
--
--   1. $z^{N,l}(T,x,y) = g(x^l,\mu^N_{x,y})$ for all $l$, $x$ and $y \in \mathbb Y$;
--   2. for all $l$, $t \in [0,T]$ and $(x,y) \in \mathcal T_N$,
--   $$
--   \frac{d}{dt}z^{N,l} + \sum_{m}\varphi(\mu^N_{x,y}[\bullet])\cdot\Delta^m z^{N,l}[\bullet] + \sum_{m\ne l}a^*(x^m, z^{N,m}_\bullet)\cdot\Delta^m z^{N,l} + H(x^l, z^{N,l}_\bullet) + f(x^l,\mu^N_{x,y}) + \varepsilon N\,\mathbf E\Big[\tfrac{S[x^l]}{N\mu^N_{x,y}[x^l]}\big(z^{N,l}(t,x,y') - z^{N,l}(t,x,y)\big)\Big] = r^{N,l}(t,x,y)
--   $$
--   with $|r^{N,l}(t,x,y)| \le C/N^\eta$.
--
--   That is, the projection of the master equation's solution onto the $N$-player state space is an approximate solution of the normalized Nash system; Theorem 2.4 is obtained by comparing it with the exact solution.
--
--   **Formalization Note.** This is the $z$-form of Remark 4.7, the version used in the proof of Theorem 2.4; the $u$-form (4.23) divides by $y^m$ and $y^l$, which may vanish on $\mathcal T_N$. The master equation carries $\varepsilon$, $\varepsilon/2$ instead of the printed $\varepsilon^2$, $\varepsilon^2/2$: with $\varepsilon^2$ the rest would contain $\varepsilon(1-\varepsilon)$ times the Wright–Fisher terms of $U$, which do not vanish as $N \to \infty$. The Wright–Fisher Hölder space is replaced by the regularity class. The time derivative is one-sided at $0$ and $T$. $C$ is chosen after all model data and $U$, before $N$ and the point.
-- source:
--   Bayraktar, Cecchin, Cohen & Delarue, Finite State Mean Field Games with Wright–Fisher Common Noise as Limits of N-Player Weighted Games, arXiv:2012.04845v2, p. 24, Proposition 4.6 and Remark 4.7, (4.23)–(4.24)

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting

open Finset

namespace WFMFG.Conv

theorem proposition_4_6 (γ' ϵ : ℝ) (hγ0 : 0 < γ') (hγ1 : γ' < 1) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1 / 4) :
    ∃ η : ℝ, 0 < η ∧
    ∀ (d : ℕ) [NeZero d] (ε T κ δ : ℝ), 0 < ε → ε < 1 → 0 < T → 0 < δ →
    ∀ φ : ℝ → ℝ, IsCutoff κ δ φ →
    ∀ f g : Fin d → (Fin d → ℝ) → ℝ,
    ∀ U : Fin d → ℝ → (Fin d → ℝ) → ℝ, IsMasterSol ε T φ f g U → WFReg γ' T U →
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      (∀ (l : Fin N) (x : Fin N → Fin d), ∀ y ∈ Yset N, zN U l T x y = g (x l) (empMeas x y)) ∧
      ∀ (l : Fin N) (t : ℝ) (x : Fin N → Fin d) (y : Fin N → ℚ),
        t ∈ Set.Icc 0 T → y ∈ Yset N → TN ϵ x y →
        ∃ r : ℝ, |r| ≤ C / (N : ℝ) ^ η ∧
          HasDerivWithinAt (fun s => zN U l s x y)
            (r - nashOp ε φ f (fun l' s x' y' => zN U l' s x' y') l t x y) (Set.Icc 0 T) t := by sorry

end WFMFG.Conv
