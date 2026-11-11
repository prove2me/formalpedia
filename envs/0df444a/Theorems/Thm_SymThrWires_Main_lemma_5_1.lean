-- Prove2me | Theorems.Thm_SymThrWires_Main_lemma_5_1
-- name    : SymThrWires.Main.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:17:06.0947+00:00
-- url     : https://prove2.me/theorems/5446516c-b0cb-46b5-87bd-77c9ac74d9ee
-- title:
--   Lemma 5.1 — cycle-sum identity: the frequency-summed trace potential is a signed weighted count of closed walks with vanishing walk sums (every m ≥ 1)
-- statement:
--   Let $m,N\ge1$ and $Q,G_1,G_2\ge0$ be integers, let $R_j:[N]^2\to\mathbb Z$ with $|R_j(e)|\le G_j$, let $M:[N]^2\to\mathbb R$, and let $S$ be a list of $Q$ samples (repetitions allowed). Put $\Omega_j=4mG_j+1$, $\Theta=\mathbb Z/\Omega_1\times\mathbb Z/\Omega_2$, $\Gamma(e)=Q-N^2|\{t:S_t=e\}|$, $\psi_\theta(e)=2\pi(\theta_1R_1(e)/\Omega_1+\theta_2R_2(e)/\Omega_2)$, $E_{\theta,0}(e)=\Gamma(e)M(e)\cos\psi_\theta(e)$ and $E_{\theta,1}(e)=\Gamma(e)M(e)\sin\psi_\theta(e)$. For a closed alternating walk $w\in[N]^{2m}$ with edges $e_1,\dots,e_{2m}$ and a sign pattern $\sigma\in\{\pm1\}^{2m}$, let $Y_{j,\sigma}(w)=\sum_l\sigma_lR_j(e_l)$, $\kappa_\sigma=1+(-1)^m\prod_l\sigma_l$, $\Gamma_w=\prod_l\Gamma(e_l)$ and $M_w=\prod_l M(e_l)$. Then
--   $$\sum_{\theta\in\Theta}\sum_{\nu=0}^1\mathrm{tr}\,H(E_{\theta,\nu})^{2m}=\frac{2|\Theta|}{4^m}\sum_w\Gamma_wM_w\sum_{\sigma\in\{\pm1\}^{2m}}\kappa_\sigma\,1[Y_{1,\sigma}(w)=0]\,1[Y_{2,\sigma}(w)=0].$$
--
--   The identity makes the sampler's potential computable as a count of closed walks with vanishing signed residual sums, which is what the algorithm evaluates exactly.
--
--   Differences from the source:
--   - encoding: walk edges e_{2i−1} = (u_i, v_i), e_{2i} = (u_{i+1}, v_i), u_{m+1} = u_1 → `walkEdge u v` indexed from 0 with u_m = u_0; reason: index shift only
--   - encoding: θ_j ∈ Z/Ω_j inside ψ_θ; σ ∈ {±1}^{2m}; |Θ| → θ_j.val (the representative in [0, Ω_j)); σ : Fin (2m) → ℤˣ; Fintype.card (ZMod Ω₁ × ZMod Ω₂); reason: R_j is integer-valued, so cos and sin do not depend on the representative; ℤˣ = {±1}
--   - encoding: the walk sum over w ∈ [N]^{2m} → a double sum over u, v : Fin m → Fin N; reason: w = (u_1, …, u_m, v_1, …, v_m)
-- source:
--   Dev Nag, Near-Cubic Gate and Near-Quartic Wire Lower Bounds for SYM∘THR Circuits, STOC 2027 submission, Zenodo doi:10.5281/zenodo.23847026 (sha256 02f54f02…), p. 17, Lemma 5.1

import Mathlib
import Definitions.Def_SymThrWires_Main_Sampling

namespace SymThrWires.Main

/-- **Lemma 5.1** (Cycle-sum identity, p. 17). Let `m, N ≥ 1` and `Q, G₁, G₂ ≥ 0`, let
`R_j : [N]² → Z` with `|R_j(e)| ≤ G_j`, let `M : [N]² → R`, and let `S` be a list of `Q` samples.
With `Ω_j = 4mG_j + 1`, `Θ = Z/Ω₁ × Z/Ω₂`, `ψ_θ(e) = 2π(θ₁R₁(e)/Ω₁ + θ₂R₂(e)/Ω₂)`,
`E_{θ,0}(e) = Γ(e)M(e) cos ψ_θ(e)` and `E_{θ,1}(e) = Γ(e)M(e) sin ψ_θ(e)`:
`Σ_θ Σ_ν tr H(E_{θ,ν})^{2m} = (2|Θ|/4^m) Σ_w Γ_w M_w Σ_σ κ_σ 1[Y_{1,σ}(w) = 0] 1[Y_{2,σ}(w) = 0]`,
the sum over closed alternating walks `w = (u, v) ∈ [N]^{2m}` and sign patterns `σ ∈ {±1}^{2m}`. -/
theorem lemma_5_1 (m N Q G₁ G₂ : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (R₁ R₂ : Fin N × Fin N → ℤ) (hR₁ : ∀ e, |R₁ e| ≤ (G₁ : ℤ)) (hR₂ : ∀ e, |R₂ e| ≤ (G₂ : ℤ))
    (M : Fin N × Fin N → ℝ) (S : Fin Q → Fin N × Fin N) :
    ∑ θ : ZMod (4 * m * G₁ + 1) × ZMod (4 * m * G₂ + 1), ∑ ν : Fin 2,
        Matrix.trace (dilation (Matrix.of fun u v =>
          sampleGamma S (u, v) * M (u, v) *
            (if ν = 0 then
              Real.cos (2 * Real.pi * ((θ.1.val : ℝ) * (R₁ (u, v) : ℝ) / ((4 * m * G₁ + 1 : ℕ) : ℝ) +
                (θ.2.val : ℝ) * (R₂ (u, v) : ℝ) / ((4 * m * G₂ + 1 : ℕ) : ℝ)))
            else
              Real.sin (2 * Real.pi * ((θ.1.val : ℝ) * (R₁ (u, v) : ℝ) / ((4 * m * G₁ + 1 : ℕ) : ℝ) +
                (θ.2.val : ℝ) * (R₂ (u, v) : ℝ) / ((4 * m * G₂ + 1 : ℕ) : ℝ))))) ^ (2 * m)) =
      2 * (Fintype.card (ZMod (4 * m * G₁ + 1) × ZMod (4 * m * G₂ + 1)) : ℝ) / 4 ^ m *
        ∑ u : Fin m → Fin N, ∑ v : Fin m → Fin N,
          (∏ l, sampleGamma S (walkEdge u v l)) * (∏ l, M (walkEdge u v l)) *
            ∑ σ : Fin (2 * m) → ℤˣ, (kappa σ : ℝ) *
              (if ∑ l, ((σ l : ℤˣ) : ℤ) * R₁ (walkEdge u v l) = 0 then 1 else 0) *
              (if ∑ l, ((σ l : ℤˣ) : ℤ) * R₂ (walkEdge u v l) = 0 then 1 else 0) := by sorry

end SymThrWires.Main
