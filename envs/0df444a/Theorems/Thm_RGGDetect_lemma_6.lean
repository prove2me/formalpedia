-- Prove2me | Theorems.Thm_RGGDetect_lemma_6
-- name    : RGGDetect.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:09.664563+00:00
-- url     : https://prove2.me/theorems/5f9f938e-d66f-40be-8d71-182dc2f49f43
-- title:
--   Lemma 6 — bad denominator estimate
-- statement:
--   Assume $|V|\le B^*$, where $B^*$ is the slack of (37), and let $I=V^c$. For every nonzero $D\in\mathcal H_{\boldsymbol\ell}$,
--
--   $$
--   \mathbb E\left[\int_{T_I\cap\{\Lambda_{u,I}<1/2\}}\frac{r^2_{u,I,D}}{\Lambda_{u,I}}\,dQ_I\right]\le C\,\mathbb E(D^2)\,\phi_{\nu(D)}(\Delta), \tag{41}
--   $$
--
--   where $C$ only depends on $t(D)$.
--
--   The rare event that the external-edge likelihood ratio is small is controlled by the truncated $\chi^2$-divergence $\Delta$ itself, which feeds the self-bounding scheme.
--
--   **Formalization Note** Non-asymptotic: $C>0$ is chosen after $t$; the bound holds for every $n$, $d\ge1$, $\tau$ with $0<p<1$, slack $B\ge|V|$ and $u\in V$, with $\Delta$ the quantity (9) for the same $n$ and $B$.
--
--   Differences from the source:
--   - encoding: the model's dimension d and edge density p → d ≥ 1 and τ with 0 < p = P{⟨x₁, x₂⟩ ≥ τ} < 1; reason: nondegeneracy only: for d = 0 the sphere is empty, and κ, Q_I, Λ_{u,I} are undefined at p ∈ {0, 1}
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Lemma 6, eq. (41), p.15 (PDF p.17)

import Mathlib
import Definitions.Def_RGGDetect_cavity
import Definitions.Def_RGGDetect_harmPoly
import Definitions.Def_RGGDetect_Delta

open MeasureTheory

namespace RGGDetect

/-- **Lemma 6** (bad denominator estimate; arXiv:2610.08517, held version, sha256 e7bebd4a…, Lemma 6,
p.15, eq. (41)): assume `|V| ≤ B*`, where `B*` is the slack of (37). For every nonzero `D ∈ H_ℓ`,
`E[∫_{T_I ∩ {Λ_{u,I} < 1/2}} r²_{u,I,D}/Λ_{u,I} dQ_I] ≤ C E(D²) ϕ_{ν(D)}(Δ)`, where `C` only depends on
`t(D)`.

**Formalization Note** Non-asymptotic: `C` is chosen after `t` (with `‖ℓ‖₁ = 2t`), and the inequality
holds for every `n`, `d ≥ 1`, `τ` with `0 < p < 1`, slack `B ≥ |V|`, and `u ∈ V`; `Δ` is (9) for the
same `n` and `B`. `I = V^c`. -/
theorem lemma_6 (t : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ, 1 ≤ d → ∀ τ : ℝ, 0 < capProb d τ →
    capProb d τ < 1 → ∀ B : ℕ, ∀ (V : Finset (Fin n)) (ℓ : Fin n → ℕ), V.card ≤ B →
    (∀ v ∈ V, 1 ≤ ℓ v) → ∑ v ∈ V, ℓ v = 2 * t → ∀ D : Config n d → ℝ, D ∈ tensorHarm V ℓ →
    D ≠ 0 → ∀ u ∈ V,
      cavInt n d τ u Vᶜ D
          (fun g y => y ∈ TI n (capProb d τ) Vᶜ ∧ lamUI n d τ u Vᶜ g y < 1 / 2) ≤
        C * (∫ x, D x ^ 2 ∂(prior n d)) * phi (nuD V ℓ D) (Delta n d τ B) := by sorry

end RGGDetect
