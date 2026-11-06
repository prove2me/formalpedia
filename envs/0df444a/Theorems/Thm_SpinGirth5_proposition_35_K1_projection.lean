-- Prove2me | Theorems.Thm_SpinGirth5_proposition_35_K1_projection
-- name    : SpinGirth5.proposition_35_K1_projection
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:43.193912+00:00
-- url     : https://prove2.me/theorems/57495a0c-a055-4072-bb9f-103317688247
-- title:
--   Proposition 35 — $\|\operatorname{proj}_{K_1}(P_vh\,L)\|^2\le(1+O_\alpha(1/\Delta))\frac{1-\varepsilon}{\Delta}\|h\|^2$ on $K_0$
-- statement:
--   For every $\alpha\ge1$ there is $C>0$ depending only on $\alpha$ such that the following holds. Let $\nu$ be the star law (16) with leaf laws $p_1,\dots,p_d$, $d\le\Delta$, satisfying Condition 26 with $\Delta\ge2\alpha$, and let $L=L_\rho$ be the likelihood ratio. Then every $h\in K_0$ satisfies, in $L^2(\nu)$,
--   $$\big\|\operatorname{proj}_{K_1}(P_vh\cdot L)\big\|^2\le\Big(1+\frac C\Delta\Big)\cdot\frac{1-\varepsilon}{\Delta}\cdot\|h\|^2 .$$
--   Together with Proposition 36 it gives the bound (15) on $\|(P_v)_{10}\|^2$; this is where the $\varepsilon$-contraction of Condition 26 enters.
--
--   Differences from the source:
--   - generalization: ν = µ^τ_{G,N[v]}, p_i = µ^τ_{G−v,i} built from a graph (13) → any multi-spin system (A, λ), any distributions p_1, …, p_d on [q], ν the star law (16) with positive normalizer; reason: the §5 proofs use only (16) and Condition 26; (13) is an instance by p.21
--   - encoding: O_α(·) → ∃ C > 0 chosen after α and before every other datum; reason: the paper's convention: implicit constants depend on α only (§2.1, p.10)
--   - reading: d = |N(v)| with Δ the maximum degree → hypothesis d ≤ Δ; reason: Δ is the maximum degree of G and d = deg(v) (§5, p.19); the proof uses it (p.25 and (31), p.29) and Propositions 32, 36 state it
--   - encoding: ‖proj_{K₁} g‖² → ⟨g, k⟩_ν² ≤ c ⟨k, k⟩_ν for every k ∈ K₁; reason: the squared norm of the projection is the supremum of ⟨g,k⟩²/⟨k,k⟩ over k ∈ K₁
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, Proposition 35, Eq. (29), p.27

import Mathlib
import Definitions.Def_SpinGirth5_starModel

namespace SpinGirth5

/-- **Proposition 35**. For every `α ≥ 1` there is `C > 0` (depending on `α` only) such that, for
the star law `ν` of (16) with leaf laws `p_1, …, p_d` (`d ≤ Δ`), under Condition 26 and `Δ ≥ 2α`,
every `h ∈ K₀` satisfies
`‖proj_{K₁}(P_v h · L)‖² ≤ (1 + C/Δ) · ((1 − ε)/Δ) · ‖h‖²`,
where `L = L_ρ` is the likelihood ratio of Definition 28 and all norms are in `L²(ν)`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, Proposition 35, Eq. (29), p.27.

**Formalization Note** `(1 + O_α(1/Δ))` is `1 + C/Δ` with `C` chosen after `α` and before every
other datum. `‖proj_{K₁} g‖² ≤ c` is written as `⟨g, k⟩_ν² ≤ c ⟨k, k⟩_ν` for every `k ∈ K₁`.
`d ≤ Δ` is §5's standing fact that `d = |N(v)|` is at most the maximum degree `Δ` (p.19). -/
theorem proposition_35_K1_projection (α : ℝ) (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (q d Δ : ℕ) (S : Interaction q) (p : Fin d → Fin q → ℝ),
      (∀ i, MarkovMixing.IsDist (p i)) → 0 < ∑ x, starWeight S p x → d ≤ Δ →
      Condition26 S p (centerMarginal (starDist S p)) α ε Δ → 2 * α ≤ Δ →
      ∀ h k : (Option (Fin d) → Fin q) → ℝ, K0 (starDist S p) h → K1 (starDist S p) k →
        MarkovMixing.innerPi (starDist S p)
            (fun x => heatBath (starDist S p) none h x * likelihoodRatio S p (leafCfg x)) k ^ 2 ≤
          (1 + C / Δ) * ((1 - ε) / Δ) * MarkovMixing.innerPi (starDist S p) h h *
            MarkovMixing.innerPi (starDist S p) k k := by sorry

end SpinGirth5
