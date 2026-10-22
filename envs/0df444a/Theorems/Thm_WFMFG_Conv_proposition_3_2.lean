-- Prove2me | Theorems.Thm_WFMFG_Conv_proposition_3_2
-- name    : WFMFG.Conv.proposition_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:15.30703+00:00
-- url     : https://prove2.me/theorems/95f32f5f-6ed7-4ad6-a35f-b553aa2facef
-- title:
--   Proposition 3.2, p. 18 — the normalized Nash values are bounded by $T\|f\|_\infty + \|g\|_\infty$, the feedbacks by $2T\|f\|_\infty + 2\|g\|_\infty$
-- statement:
--   Let $d, N \ge 1$, $\varepsilon \in (0,1)$, $T > 0$, $\delta > 0$, let $\varphi$ be a cutoff (2.2), and let $M_f, M_g$ be bounds of $|f|$ and $|g|$ on $[\![d]\!] \times \mathcal S_{d-1}$. If $w = (w^{N,l})_l$ is a bounded classical solution of the normalized Nash system (3.2)–(3.3), then for every $l$, $x \in [\![d]\!]^N$, $y \in \mathbb Y$, $t \in [0,T]$ and $j \in [\![d]\!]$,
--   $$
--   |w^{N,l}(t,x,y)| \le T M_f + M_g, \qquad \alpha^{*,l}(t,x,y)[j] = \big(w^{N,l}(t,x,y) - w^{N,l}(t,(j,x^{-l}),y)\big)_+ \le 2TM_f + 2M_g .
--   $$
--
--   The bound is uniform in $N$; it is the a priori estimate on which the proof of Theorem 2.4 rests.
--
--   **Formalization Note.** The paper's $\|f\|_\infty$, $\|g\|_\infty$ are replaced by arbitrary bounds $M_f, M_g$; the statement for all admissible bounds is equivalent to the printed one.
-- source:
--   Bayraktar, Cecchin, Cohen & Delarue, Finite State Mean Field Games with Wright–Fisher Common Noise as Limits of N-Player Weighted Games, arXiv:2012.04845v2, p. 18, Proposition 3.2

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial
import Definitions.Def_WFMFG_Conv_Setting

open Finset

namespace WFMFG.Conv

theorem proposition_3_2 (d N : ℕ) [NeZero d] (hN : 1 ≤ N) (ε T κ δ Mf Mg : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hT : 0 < T) (hδ : 0 < δ)
    (φ : ℝ → ℝ) (hφ : IsCutoff κ δ φ) (f g : Fin d → (Fin d → ℝ) → ℝ)
    (hf : ∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), |f i p| ≤ Mf)
    (hg : ∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), |g i p| ≤ Mg)
    (w : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ) (hw : IsNashSol N ε T φ f g w) :
    ∀ (l : Fin N) (x : Fin N → Fin d), ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T,
      |w l t x y| ≤ T * Mf + Mg ∧
      ∀ j : Fin d, astar (x l) (fun j' => w l t (Function.update x l j') y) j ≤ 2 * T * Mf + 2 * Mg := by sorry

end WFMFG.Conv
