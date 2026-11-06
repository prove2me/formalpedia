-- Prove2me | Theorems.Thm_StrongConv_exists_tendsto_uniformExp_trace_wordEval_model
-- name    : StrongConv.exists_tendsto_uniformExp_trace_wordEval_model
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T22:12:52.626877+00:00
-- url     : https://prove2.me/theorems/1c7f6ed2-b2f4-4caa-85cd-3257b1f053ad
-- title:
--   Lemma 10.2 — lim E[Tr w(Πᴺ)] = ϖ(k), with ϖ(1) = 0 and |ϖ(k)| ≤ ckᵝ for k ≥ 2
-- statement:
--   Let $\pi$ be a stable representation (`StableRep`) with no trivial summand (`NoTrivialSummand`), and let $\beta$ (`StableRep.beta`) be the degree of $\varphi(x_1, x_2^2, \dots, x_r^r)$ for its character polynomial $\varphi$. Then there are a function $\varpi : \{0, 1, 2, \dots\} \to \mathbb R$ and a constant $c$ such that:
--   1. for every $d$ and every word $w$ in the letters $g_0 = e$, $g_i$, $g_{d+i} = g_i^{-1}$ whose reduction $w(g_1, \dots, g_d)$ (`wordFree w`) is not the identity, if $w(g_1, \dots, g_d) = v^k$ with $v \in \mathbf F_d$ a non-power (`IsNonPower`) and $k \ge 1$, then $$\lim_{N\to\infty} \mathbf E[\operatorname{Re}\mathrm{Tr}\, w(\boldsymbol\Pi^N)] = \varpi(k);$$
--   2. $\varpi(1) = 0$;
--   3. $|\varpi(k)| \le c\,k^\beta$ for every $k \ge 2$.
--
--   Here $\boldsymbol\Pi^N = (\pi_N(\sigma_1), \dots, \pi_N(\sigma_d))$ (`StableRep.model`) for i.i.d. uniform $\sigma_1, \dots, \sigma_d \in \mathbf S_N$, $w(\boldsymbol\Pi^N)$ is `wordEval`, and $\mathrm{Tr}$ is the trace on $\mathbb C^{D_N}$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 31, Lemma 10.2

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4

open Filter Topology

namespace StrongConv

theorem exists_tendsto_uniformExp_trace_wordEval_model (π : StableRep) (hπ : π.NoTrivialSummand) :
    ∃ (ϖ : ℕ → ℝ) (c : ℝ),
      (∀ (d : ℕ) (w : List (Letter d)), wordFree w ≠ 1 → ∀ (v : FreeGroup (Fin d)) (k : ℕ),
        IsNonPower v → 1 ≤ k → wordFree w = v ^ k →
        Tendsto (fun N : ℕ => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
            (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
              (wordEval (π.model σ) w :
                EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)))).re))
          atTop (𝓝 (ϖ k))) ∧
      ϖ 1 = 0 ∧ ∀ k : ℕ, 2 ≤ k → |ϖ k| ≤ c * (k : ℝ) ^ π.beta := by
  sorry

end StrongConv
