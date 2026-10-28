-- Prove2me | Theorems.Thm_WHAdditivity_Renyi_trace_marginal_product
-- name    : WHAdditivity.Renyi.trace_marginal_product
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:25:58.940377+00:00
-- url     : https://prove2.me/theorems/22ccdca3-84c5-428d-a896-7e9381ef39ad
-- title:
--   (8), p. 3, second line — Tr((ρ_Λ ⊗ 𝟙_Λᶜ)(ρ_Λ′ ⊗ 𝟙_Λ′ᶜ)) = (∏_{j∈(Λ∪Λ′)ᶜ} dⱼ) Tr ρ²_{Λ∩Λ′}
-- statement:
--   Let $N\in\mathbb N$, let $d_1,\dots,d_N$ be dimensions, and let $\rho$ be any complex matrix on $\bigotimes_{j=1}^N\mathbb C^{d_j}$. For $\Lambda\subset\{1,\dots,N\}$ write $\rho_\Lambda = \operatorname{Tr}_{\Lambda^{\mathrm c}}\rho$ for its reduced matrix on the sites in $\Lambda$, and $\rho_\Lambda\otimes\mathbb 1_{\Lambda^{\mathrm c}}$ for its tensor product with the identity on the other sites. Then for all $\Lambda,\Lambda'\subset\{1,\dots,N\}$
--
--   $$\operatorname{Tr}\Bigl(\bigl(\rho_\Lambda\otimes\mathbb 1_{\Lambda^{\mathrm c}}\bigr)\bigl(\rho_{\Lambda'}\otimes\mathbb 1_{\Lambda'^{\mathrm c}}\bigr)\Bigr) = \Bigl(\prod_{j\in(\Lambda\cup\Lambda')^{\mathrm c}} d_j\Bigr)\operatorname{Tr}\rho_{\Lambda\cap\Lambda'}^2 .$$
--
--   In the paper $\rho$ is $|\bar\Omega\rangle\langle\bar\Omega|$, and this identity, summed over $\Lambda,\Lambda'$ with the signs $(-1)^{|\Lambda|+|\Lambda'|}$, is the step from the first to the second line of the computation (8) of $\operatorname{Tr}X_N(\Omega)^2$.
--
--   **Formalization Note.** The complement $\Lambda^{\mathrm c}$ is taken in $\{1,\dots,N\}$ (the `Finset` complement in `Fin N`). The product over the empty set is $1$, and $\rho_\emptyset$ is the $1\times1$ matrix $(\operatorname{Tr}\rho)$.
--
--   Differences from the source:
--   - generalization: ρ_Λ the reduced density matrix of |Ω̄⟩⟨Ω̄| for a unit vector Ω → ρ_Λ the reduced matrix of an arbitrary complex matrix ρ; reason: the identity holds for every ρ, and ρ = |Ω̄⟩⟨Ω̄| is the paper's case.
--   - generalization: N ≥ 1 implicitly, d_j ≥ 2 → every N ∈ ℕ and every d_j; reason: the identity holds for all dimensions; it specializes to the paper's.
--   - encoding: sites 1, …, N → sites `Fin N` from 0, tensor factors in site order; reason: relabelling only.
-- source:
--   Alicki, Fannes, Note on multiple additivity of minimal Renyi entropy output of the Werner–Holevo channels, arXiv:quant-ph/0407033v2, p. 3, (8), first and second lines

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace WHAdditivity.Renyi

theorem trace_marginal_product (N : ℕ) (d : Fin N → ℕ) (ρ : Matrix (Config d) (Config d) ℂ)
    (Λ Λ' : Finset (Fin N)) :
    (tensorIdentity d Λ (reducedMatrix d Λ ρ) * tensorIdentity d Λ' (reducedMatrix d Λ' ρ)).trace =
      (∏ j ∈ (Λ ∪ Λ')ᶜ, (d j : ℂ)) * (reducedMatrix d (Λ ∩ Λ') ρ ^ 2).trace := by sorry

end WHAdditivity.Renyi
