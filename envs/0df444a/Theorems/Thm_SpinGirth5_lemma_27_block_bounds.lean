-- Prove2me | Theorems.Thm_SpinGirth5_lemma_27_block_bounds
-- name    : SpinGirth5.lemma_27_block_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:13:17.383263+00:00
-- url     : https://prove2.me/theorems/a642d188-fcc3-4b1b-96a9-23aaa232b48b
-- title:
--   Lemma 27 — $\|(P_v)_{00}\|\le O_\alpha(1/\Delta)$ and $\|(P_v)_{10}\|^2\le(1+O_\alpha(1/\Delta))\frac{1-\varepsilon}{\Delta}+O_\alpha(\sqrt{\log 2d}/\Delta^{3/2})$
-- statement:
--   For every $\alpha\ge1$ there is $C>0$ depending only on $\alpha$ such that the following holds. Let $\nu$ be the star law (16) with leaf laws $p_1,\dots,p_d$, satisfying Condition 26, with $1\le d\le\Delta$ and $\Delta\ge2\alpha$. Then on $(\mathbf 1^\perp,\langle\cdot,\cdot\rangle_\nu)$,
--   $$\|(P_v)_{00}\|\le\frac C\Delta,\tag{14}$$
--   $$\|(P_v)_{10}\|^2\le\Big(1+\frac C\Delta\Big)\frac{1-\varepsilon}{\Delta}+C\,\frac{\sqrt{\log(2d)}}{\Delta^{3/2}}.\tag{15}$$
--   These are the two block norms that Theorem 25 needs; with them, Theorem 25 gives the local weighted spectral gaps of Theorem 20 for $\eta_v=(1-\varepsilon/2)/\Delta$.
--
--   Differences from the source:
--   - generalization: ν = µ^τ_{G,N[v]}, p_i = µ^τ_{G−v,i} built from a graph (13) → any multi-spin system (A, λ), any distributions p_1, …, p_d on [q], ν the star law (16) with positive normalizer; reason: the §5 proofs use only (16) and Condition 26; (13) is an instance by p.21
--   - encoding: O_α(·) → ∃ C > 0 chosen after α and before every other datum; reason: the paper's convention: implicit constants depend on α only (§2.1, p.10)
--   - reading: d = |N(v)| with Δ the maximum degree → hypothesis d ≤ Δ; reason: Δ is the maximum degree of G and d = deg(v) (§5, p.19); the proof uses it (p.25 and (31), p.29) and Propositions 32, 36 state it
--   - encoding: operator norms of blocks ‖·‖ (Definition 11) → quadratic-form bounds over h ∈ K₀, k ∈ K₁; reason: ‖(P_v)₀₀‖ is the top Rayleigh quotient of the positive semidefinite block on K₀; ‖proj_{K₁} g‖² ≤ c ⟺ ⟨g,k⟩² ≤ c⟨k,k⟩ for all k ∈ K₁
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, Lemma 27, Eqs. (14)–(15), p.20

import Mathlib
import Definitions.Def_SpinGirth5_starModel

namespace SpinGirth5

/-- **Lemma 27** (block bounds for the centre projection). For every `α ≥ 1` there is `C > 0`
(depending on `α` only) such that, for the star law `ν` of (16) with leaf laws `p_1, …, p_d`, if
Condition 26 holds, `1 ≤ d ≤ Δ` and `Δ ≥ 2α`, then on `(1⊥, ⟨·,·⟩_ν)`
* `‖(P_v)₀₀‖ ≤ C/Δ`  (14);
* `‖(P_v)₁₀‖² ≤ (1 + C/Δ) · (1 − ε)/Δ + C √(log(2d)) / Δ^{3/2}`  (15).

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, Lemma 27, Eqs. (14)–(15), p.20.

**Formalization Note** One `C` serves all three `O_α` terms; it is chosen after `α` and before
every other datum. `(P_v)₀₀` is self-adjoint and positive semidefinite on `K₀`, so (14) is
`⟨h, P_v h⟩ ≤ (C/Δ)⟨h, h⟩` for `h ∈ K₀`; (15) is `⟨P_v h, k⟩² ≤ c ⟨h, h⟩⟨k, k⟩` for `h ∈ K₀`,
`k ∈ K₁`. `d ≤ Δ` is §5's standing fact that `d = |N(v)|` is at most the maximum degree `Δ`
(p.19). -/
theorem lemma_27_block_bounds (α : ℝ) (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (q d Δ : ℕ) (S : Interaction q) (p : Fin d → Fin q → ℝ),
      (∀ i, MarkovMixing.IsDist (p i)) → 0 < ∑ x, starWeight S p x → 1 ≤ d → d ≤ Δ →
      Condition26 S p (centerMarginal (starDist S p)) α ε Δ → 2 * α ≤ Δ →
      (∀ h, K0 (starDist S p) h →
        MarkovMixing.innerPi (starDist S p) h (heatBath (starDist S p) none h) ≤
          C / Δ * MarkovMixing.innerPi (starDist S p) h h) ∧
      (∀ h k, K0 (starDist S p) h → K1 (starDist S p) k →
        MarkovMixing.innerPi (starDist S p) (heatBath (starDist S p) none h) k ^ 2 ≤
          ((1 + C / Δ) * ((1 - ε) / Δ) + C * Real.sqrt (Real.log (2 * d)) / (Δ : ℝ) ^ ((3 : ℝ) / 2)) *
            MarkovMixing.innerPi (starDist S p) h h * MarkovMixing.innerPi (starDist S p) k k) := by sorry

end SpinGirth5
