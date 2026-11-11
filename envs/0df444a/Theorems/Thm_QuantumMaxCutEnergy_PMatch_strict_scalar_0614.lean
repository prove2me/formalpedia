-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PMatch_strict_scalar_0614
-- name    : QuantumMaxCutEnergy.PMatch.strict_scalar_0614
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:32:35.957287+00:00
-- url     : https://prove2.me/theorems/bc9f61cf-ace7-4264-8d75-9486b3c76d31
-- title:
--   Scalar certificate $0.6141$ for the partially entangled matching mixture at $d=2000/2001$
-- statement:
--   For $u\in[0,1]$ let $m=\max\{(3u-1)/2,0\}$, $d=2000/2001$, $\sigma=10920/38809$, $\kappa=37241/38809$ (so $\sigma^2+\kappa^2=1$) and $F=0.84882\,u+0.084882\,u^3+0.027283\,u^5$. Then
--
--   $$0.6141\cdot\frac{1+3u}{2}\le 0.88\Bigl(\tfrac12+\tfrac\sigma2dm+\bigl(\tfrac{\kappa^2}{2}+\tfrac{\sigma(1+\sigma)}{2}dm\bigr)F\Bigr)+0.12\Bigl(\tfrac12+\tfrac32dm\Bigr).$$
--
--   Here $u=-s$ for an edge with Pauli correlation $s\le 0$, $(1+3u)/2$ is its relaxation value, $F$ is a lower bound for the rank-three rounding function, and the two brackets are the per-edge energies of the partially entangled matching state and of the matching state.
-- source:
--   Apte, Lee, Marwaha, Parekh and Sud, ESA 2025, https://doi.org/10.4230/LIPIcs.ESA.2025.101, Eqs. (19)-(24), in the form of arXiv:2504.15276v2, with matching-polytope factor d = 2000/2001, mixing weight 0.88 and sin(theta) = 10920/38809.

import Mathlib

theorem QuantumMaxCutEnergy.PMatch.strict_scalar_0614 (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (0.6141 : ℝ) * ((1 + 3 * u) / 2) ≤
      0.88 * (1 / 2 + (10920 / 38809 : ℝ) / 2 * ((2000 / 2001) * max ((3 * u - 1) / 2) 0) +
        ((37241 / 38809 : ℝ) ^ 2 / 2 +
          (10920 / 38809 : ℝ) * (1 + 10920 / 38809) / 2 *
            ((2000 / 2001) * max ((3 * u - 1) / 2) 0)) *
          (0.84882 * u + 0.084882 * u ^ 3 + 0.027283 * u ^ 5)) +
      (1 - 0.88) * (1 / 2 + (3 / 2) * ((2000 / 2001) * max ((3 * u - 1) / 2) 0)) := by sorry
