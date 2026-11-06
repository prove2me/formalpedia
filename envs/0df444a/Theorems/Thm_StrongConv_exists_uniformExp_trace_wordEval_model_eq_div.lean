-- Prove2me | Theorems.Thm_StrongConv_exists_uniformExp_trace_wordEval_model_eq_div
-- name    : StrongConv.exists_uniformExp_trace_wordEval_model_eq_div
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T22:12:58.076994+00:00
-- url     : https://prove2.me/theorems/22e37231-4d4d-477c-adc8-704637c7b22a
-- title:
--   Lemma 10.1 — for a stable representation, the expected trace of a word is a rational function of 1/N
-- statement:
--   Let $\pi$ be a stable representation (`StableRep`) with no trivial summand (`NoTrivialSummand`), with character polynomial $\varphi \in \mathbb C[x_1, \dots, x_r]$, and let $\beta$ (`StableRep.beta`) be the degree of $\varphi(x_1, x_2^2, \dots, x_r^r)$. Let $d, q \ge 0$, and let $w$ be a word of length at most $q$ in the letters $g_0 = e$, $g_i$, $g_{d+i} = g_i^{-1}$ whose reduction $w(g_1, \dots, g_d) \in \mathbf F_d$ (`wordFree w`) is not the identity. Then $g_{\beta q}(x) = \prod_{j=1}^{\beta q - 1}(1 - jx)^{\min(d, \lfloor \beta q/(j+1)\rfloor)}$ (`gPoly d (β * q)`) has degree at most $\beta q(1 + \log d)$, and there is a real polynomial $f_w$ of degree at most $\beta q(1 + \log d)$ such that for every $N \ge \max\{\beta q, N_0\}$
--   $$\mathbf E[\operatorname{Re}\mathrm{Tr}\, w(\boldsymbol\Pi^N)] = \frac{f_w(1/N)}{g_{\beta q}(1/N)}.$$
--   Here $\boldsymbol\Pi^N = (\pi_N(\sigma_1), \dots, \pi_N(\sigma_d))$ (`StableRep.model`) for i.i.d. uniform $\sigma_1, \dots, \sigma_d \in \mathbf S_N$, $w(\boldsymbol\Pi^N)$ is `wordEval`, and $\mathrm{Tr}$ is the trace on $\mathbb C^{D_N}$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 30, Lemma 10.1

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4

open Polynomial

namespace StrongConv

theorem exists_uniformExp_trace_wordEval_model_eq_div (π : StableRep) (hπ : π.NoTrivialSummand)
    (d q : ℕ) (w : List (Letter d)) (hw : w.length ≤ q) (hw1 : wordFree w ≠ 1) :
    ((gPoly d (π.beta * q)).natDegree : ℝ) ≤ π.beta * q * (1 + Real.log d) ∧
      ∃ f : ℝ[X], (f.natDegree : ℝ) ≤ π.beta * q * (1 + Real.log d) ∧
        ∀ N : ℕ, π.beta * q ≤ N → π.N₀ ≤ N →
          uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
              (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
                (wordEval (π.model σ) w :
                  EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)))).re) =
            f.eval (1 / (N : ℝ)) / (gPoly d (π.beta * q)).eval (1 / (N : ℝ)) := by
  sorry

end StrongConv
