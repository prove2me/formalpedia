-- Prove2me | Theorems.Thm_RGGDetect_proposition_1
-- name    : RGGDetect.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:41:14.191206+00:00
-- url     : https://prove2.me/theorems/7b07ae89-d329-4658-872d-60fad71dd38f
-- title:
--   Proposition 1 — the cavity recurrence (68)
-- statement:
--   Let $K$ and $M$ satisfy (67): $M\ge K$, $K>2/\delta$, $\delta(3M+4-k)>1$ for $1\le k<K$, and $\delta(M+4)>1$. For every $D=D(x_V)\in\mathcal H_{\boldsymbol\ell}$ fix $u\in V$, let $h=\ell_u$, and assume $|V|\le B^*$. Then
--
--   $$
--   \mathrm{Post}(D)\le Cg(D)+C\,\mathbb E(D^2)\phi_{\nu(D)}(\Delta)+C\sum_{\mathbf a\in\mathcal A^*_{K,M}(h)}\ \sum_{S\subseteq V^c:|S|=|\mathbf a|}\frac{p^{|\mathbf a|}L^{\|\mathbf a\|_1}}{d^h}\,\mathrm{Post}(T^{u,S}_{\mathbf a}D)+o(g(D)), \tag{68}
--   $$
--
--   where $|\mathbf a|$ is the length of $\mathbf a$, $\mathcal A^*_{K,M}(h)=\bigcup_{k=1}^{K-1}\mathcal A_{k,M}(h)$ (66), and $C$ only depends on $|V|,t(D),K,M$.
--
--   The posterior moment of one harmonic is bounded by posterior moments of harmonics of controlled multidegree, plus the target scale and a $\Delta$ term.
--
--   **Formalization Note** In the regime (1), for every slack $B^*$. $C>0$ is chosen after $\delta,K,M,B^*$ and a bound $T$ on $t(D)$, before the sequences; $o(g(D))$ is $e_n\,g(D)$ with $e_n\to0$ chosen after the sequences, uniform over every $V$ with $|V|\le B^*$, positive $\boldsymbol\ell$ with $\|\boldsymbol\ell\|_1=2t\le2T$, nonzero $D\in\mathcal H_{\boldsymbol\ell}$ and $u\in V$. The double sum over $\mathbf a$ and $S$ is a sum over $S\subseteq V^c$ with $1\le|S|<K$ and multidegrees $\mathbf a\in\mathcal A_{|S|,M}(h)$ indexed by $S$.
--
--   Differences from the source:
--   - generalization: the standing hypotheses (1) of Theorem 1, for all n → sequences in `Regime δ p d τ`: each hypothesis for all large n; reason: the statement is asymptotic, so sequences satisfying (1) for all n are covered
--   - encoding: Σ over a ∈ A*_{K,M}(h) and S ⊆ V^c with |S| = |a| → Σ over S ⊆ V^c with 1 ≤ |S| < K and a ∈ A_{|S|,M}(h) indexed by S; reason: the same terms through the increasing ordering of S
--   - encoding: C depending only on |V|, t(D), K, M; o(g(D)) → C > 0 chosen after δ, K, M, B* and a bound T on t(D), before the sequences; e_n·g(D) with e → 0 after the sequences, uniform over the class; reason: the paper's conventions (p.2); uniformity is what Proposition 2 uses (p.22)
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Proposition 1, eq. (68), p.20 (PDF p.22)

import Mathlib
import Definitions.Def_RGGDetect_Regime
import Definitions.Def_RGGDetect_Delta
import Definitions.Def_RGGDetect_harmCoef

open Filter Topology MeasureTheory

namespace RGGDetect

/-- **Proposition 1** (cavity recurrence; arXiv:2610.08517, held version, sha256 e7bebd4a…,
Proposition 1, p.20, eq. (68)): let `K, M` satisfy (67). For every `D = D(x_V) ∈ H_ℓ`, fix `u ∈ V`,
`h = ℓ_u`, and assume `|V| ≤ B*`. Then
`Post(D) ≤ C g(D) + C E(D²) ϕ_{ν(D)}(Δ) + C ∑_{a ∈ A*_{K,M}(h)} ∑_{S ⊆ V^c : |S| = |a|}
(p^{|a|} L^{‖a‖₁}/d^h) Post(T^{u,S}_a D) + o(g(D))`, with `C` depending only on `|V|, t(D), K, M`.

**Formalization Note** In the regime (1), for `K, M` satisfying (67) and every slack `B* = B`. `C` is
chosen after `δ, K, M, B` and a bound `T` on `t(D)`, before the sequences; the `o(g(D))` is `e_n g(D)`
with `e → 0` chosen after the sequences, uniform over every `V` with `|V| ≤ B`, positive multidegree
`ℓ` with `‖ℓ‖₁ = 2t ≤ 2T`, nonzero `D ∈ H_ℓ` and `u ∈ V`. The double sum over `a ∈ A*_{K,M}(h)` (tuples
of length `1 ≤ k < K`) and `S` with `|S| = |a|` is written as a sum over `S ⊆ V^c` with `1 ≤ |S| < K`
and `a ∈ A_{|S|,M}(h)` indexed by `S` (the same terms, through the increasing ordering of `S`). -/
theorem proposition_1 (δ : ℝ) (hδ : 0 < δ) (K M B : ℕ) (h67a : K ≤ M) (h67b : (K : ℝ) > 2 / δ)
    (h67c : ∀ k : ℕ, 1 ≤ k → k < K → δ * (3 * (M : ℝ) + 4 - k) > 1)
    (h67d : δ * ((M : ℝ) + 4) > 1) (T : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : ℕ → ℝ) (d : ℕ → ℕ) (τ : ℕ → ℝ), Regime δ p d τ →
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      ∀ (V : Finset (Fin n)) (ℓ : Fin n → ℕ), V.card ≤ B → (∀ v ∈ V, 1 ≤ ℓ v) →
      (∃ t : ℕ, t ≤ T ∧ ∑ v ∈ V, ℓ v = 2 * t) →
      ∀ D : Config n (d n) → ℝ, D ∈ tensorHarm V ℓ → D ≠ 0 → ∀ u ∈ V,
        Post (τ n) D ≤ C * gD (τ n) V ℓ D +
          C * (∫ x, D x ^ 2 ∂(prior n (d n))) * phi (nuD V ℓ D) (Delta n (d n) (τ n) B) +
          C * ∑ S ∈ (Vᶜ).powerset.filter (fun S => 1 ≤ S.card ∧ S.card < K),
            ∑ a ∈ multiIdx S M (ℓ u),
              p n ^ S.card * Real.log (1 / p n) ^ (∑ i ∈ S, a i) / (d n : ℝ) ^ (ℓ u) *
                Post (τ n) (opT (d n) (ℓ u) u S a D) +
          e n * gD (τ n) V ℓ D := by sorry

end RGGDetect
