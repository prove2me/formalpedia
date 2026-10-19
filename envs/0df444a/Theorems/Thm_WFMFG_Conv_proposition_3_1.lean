-- Prove2me | Theorems.Thm_WFMFG_Conv_proposition_3_1
-- name    : WFMFG.Conv.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:16.608992+00:00
-- url     : https://prove2.me/theorems/104c300c-d8ba-4655-8679-5099b6f5fc43
-- title:
--   Proposition 3.1, p. 16 — the normalized Nash system (3.2)–(3.3) has a unique bounded solution
-- statement:
--   Let $d, N \ge 1$, $\varepsilon \in (0,1)$, $T > 0$, $\delta > 0$, let $\varphi$ be a cutoff (2.2) with parameters $\kappa, \delta$, and let $f, g : [\![d]\!] \times \mathcal S_{d-1} \to \mathbb R$ be bounded. Then the normalized Nash system (3.2) with terminal condition (3.3),
--   $$
--   \frac{d}{dt} w^{N,l} + \sum_{m}\varphi(\mu^N_{x,y}[\bullet])\cdot\Delta^m w^{N,l}[\bullet] + \sum_{m\ne l} a^*(x^m, w^{N,m}_\bullet)\cdot \Delta^m w^{N,l} + H(x^l, w^{N,l}_\bullet) + f(x^l,\mu^N_{x,y}) + \varepsilon N\,\mathbf E\Big[\tfrac{S[x^l]}{N\mu^N_{x,y}[x^l]}\big(w^{N,l}(t,x,y') - w^{N,l}(t,x,y)\big)\Big] = 0,
--   $$
--   $w^{N,l}(T,x,y) = g(x^l,\mu^N_{x,y})$, has a solution among the $N$-tuples of functions of $(t, x, y) \in [0,T] \times [\![d]\!]^N \times \mathbb Y$ with
--   $$
--   \max_{l} \sup_{t,x,y} |w^{N,l}(t,x,y)| < \infty,
--   $$
--   and any two such solutions coincide on $[0,T] \times [\![d]\!]^N \times \mathbb Y$.
--
--   This well-posedness result defines the normalized equilibrium values $w^{N,l}$ that Theorem 2.4 compares with the master equation.
--
--   **Formalization Note.** A solution is classical in $t$ (one-sided derivatives at $0$ and $T$). The functions are defined on all of $\mathbb R \times [\![d]\!]^N \times \mathbb Q^N$, so uniqueness is asserted only on $[0,T] \times [\![d]\!]^N \times \mathbb Y$. The standing Hölder assumptions on $f, g$ (Proposition 2.1) are replaced by boundedness on the simplex.
-- source:
--   Bayraktar, Cecchin, Cohen & Delarue, Finite State Mean Field Games with Wright–Fisher Common Noise as Limits of N-Player Weighted Games, arXiv:2012.04845v2, p. 16, Proposition 3.1

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting

open Finset

namespace WFMFG.Conv

theorem proposition_3_1 (d N : ℕ) [NeZero d] (hN : 1 ≤ N) (ε T κ δ Mf Mg : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hT : 0 < T) (hδ : 0 < δ)
    (φ : ℝ → ℝ) (hφ : IsCutoff κ δ φ) (f g : Fin d → (Fin d → ℝ) → ℝ)
    (hf : ∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), |f i p| ≤ Mf)
    (hg : ∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), |g i p| ≤ Mg) :
    ∃ w : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ, IsNashSol N ε T φ f g w ∧
      ∀ w' : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ, IsNashSol N ε T φ f g w' →
        ∀ (l : Fin N) (x : Fin N → Fin d), ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T,
          w' l t x y = w l t x y := by sorry

end WFMFG.Conv
