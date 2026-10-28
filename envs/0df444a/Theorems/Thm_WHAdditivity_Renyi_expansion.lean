-- Prove2me | Theorems.Thm_WHAdditivity_Renyi_expansion
-- name    : WHAdditivity.Renyi.expansion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:25:52.444534+00:00
-- url     : https://prove2.me/theorems/e9683d05-4125-4712-8cef-49aa35c015cb
-- title:
--   p. 3 — X_N(Ω) = ∏ⱼ 1/(dⱼ−1) Σ_Λ (−1)^|Λ| ρ_Λ ⊗ 𝟙_Λᶜ, with ρ_Λ the reduced matrix of |Ω̄⟩⟨Ω̄|
-- statement:
--   Let $N \in \mathbb N$ and $d_1,\dots,d_N \ge 2$, and let $\Omega \in \bigotimes_{j=1}^N\mathbb C^{d_j}$ be a unit vector (entangled or not). Write $\bar\Omega$ for its entrywise complex conjugate in the product basis, and for $\Lambda \subset\{1,\dots,N\}$ let $\rho_\Lambda$ be the reduced matrix of $|\bar\Omega\rangle\langle\bar\Omega|$ on the sites in $\Lambda$ (partial trace over $\Lambda^{\mathrm c}$). Then the output of the product of Werner–Holevo channels is
--
--   $$X_N(\Omega) := \bigotimes_{j=1}^N\Gamma_{d_j}\bigl(|\Omega\rangle\langle\Omega|\bigr) = \prod_{j=1}^N\frac{1}{d_j-1}\sum_{\Lambda\subset\{1,\dots,N\}}(-1)^{|\Lambda|}\,\rho_\Lambda\otimes\mathbb 1_{\Lambda^{\mathrm c}} .$$
--
--   Here $\rho_\emptyset = \operatorname{Tr}|\bar\Omega\rangle\langle\bar\Omega| = 1$, so the $\Lambda = \emptyset$ term is the identity, and $\rho_{\{1,\dots,N\}} = |\bar\Omega\rangle\langle\bar\Omega|$.
--
--   This expansion writes the output of the product channel on an arbitrary, possibly entangled, pure input in terms of the marginals of the input, which is what makes its purity computable in (8).
--
--   **Formalization Note.** $\bar\Omega$ is `star Ω`, and the conjugate matters: with $\Omega$ in place of $\bar\Omega$ the identity is false already for $N = 1$, $d = 2$, $\Omega = (1, i)/\sqrt 2$. $\bigotimes_j\Gamma_{d_j}$ is the generic matrix-unit tensor product of the definitions file applied to the family $\Gamma_{d_j}$. $\rho_\Lambda\otimes\mathbb 1_{\Lambda^{\mathrm c}}$ is taken in the natural order of sites.
--
--   Differences from the source:
--   - encoding: Γ_{d_j} with 1/(d_j − 1) → hypotheses 2 ≤ d_j; reason: (6) is undefined at d_j = 1.
--   - encoding: ⊗_j Γ_{d_j} on density matrices → the linear extension of (6), tensored through matrix units; reason: the product channel acts on entangled inputs, which needs Γ_d as a linear map; it agrees with (6) on density matrices.
--   - encoding: sites 1, …, N, ρ_Λ ⊗ 𝟙_{Λᶜ} → sites `Fin N` from 0, factors in site order; reason: relabelling only.
--   - generalization: N ≥ 1 implicitly → every N ∈ ℕ; reason: at N = 0 both sides are the 1 × 1 identity, and N ≥ 1 is the paper's statement.
-- source:
--   Alicki, Fannes, Note on multiple additivity of minimal Renyi entropy output of the Werner–Holevo channels, arXiv:quant-ph/0407033v2, p. 3, display after 'Next, we write out the action of the channel'

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace WHAdditivity.Renyi

theorem expansion (N : ℕ) (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (Ω : Config d → ℂ)
    (hΩ : IsUnitVector Ω) :
    tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω) =
      (∏ j, ((d j : ℂ) - 1)⁻¹) • ∑ Λ : Finset (Fin N),
        ((-1 : ℂ) ^ Λ.card) • tensorIdentity d Λ (reducedMatrix d Λ (pureState (star Ω))) := by sorry

end WHAdditivity.Renyi
