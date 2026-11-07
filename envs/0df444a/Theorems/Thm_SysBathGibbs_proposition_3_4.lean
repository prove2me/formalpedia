-- Prove2me | Theorems.Thm_SysBathGibbs_proposition_3_4
-- name    : SysBathGibbs.proposition_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:17.689233+00:00
-- url     : https://prove2.me/theorems/4a06f706-62c0-4870-9be6-1949ca4065eb
-- title:
--   Proposition 3.4 — KMS decomposition $\mathcal L=\mathcal L_{\mathrm{KMS}}-i[H_{\mathrm{Lamb}},\cdot]$
-- statement:
--   Let $H_n$ be a chain as in (1.2) and $\sigma=\beta/2$. With $\mathcal L_{\mathrm{KMS}}$ of (3.26), its site versions $\mathcal L_{\mathrm{KMS},x}$, the infinite-window generator $\mathcal L$ of (3.22) and the Lamb shift $H_{\mathrm{Lamb}}$ of (3.25):
--
--   1. $\Gamma^{-1}\mathcal L_{\mathrm{KMS}}\Gamma=\mathcal L_{\mathrm{KMS}}^\dagger$, and $\mathcal L_{\mathrm{KMS}}^\dagger$ is KMS-self-adjoint and nonpositive: $\operatorname{Re}\langle O,\mathcal L^\dagger_{\mathrm{KMS}}(O)\rangle_{\rho_\beta}\le0$ for every $O$;
--   2. the same holds for every $\mathcal L_{\mathrm{KMS},x}$;
--   3. $$\mathcal L(\rho)=\mathcal L_{\mathrm{KMS}}(\rho)-i[H_{\mathrm{Lamb}},\rho],\qquad \mathcal L_{\mathrm{KMS}}(\rho_\beta)=0,\qquad \mathcal L(\rho_\beta)=-i[H_{\mathrm{Lamb}},\rho_\beta].$$
--
--   The KMS part is detailed balanced with stationary state $\rho_\beta$; the Lamb shift is the only obstruction to $\rho_\beta$ being stationary for $\mathcal L$.
--
--   Differences from the source:
--   - encoding: σ a free parameter of (1.4)–(1.8) → σ = β/2 throughout; reason: the paper fixes σ = β/2 throughout (p.10); no other width is stated
--   - encoding: a chain [n] of qudits of dimension 2^q → n ≥ 1 and q ≥ 1 as hypotheses; reason: a chain has a site and a qudit has q ≥ 1 qubits; Q = 4^q − 1 ≥ 1 is used throughout
--   - encoding: "L†_KMS is nonpositive" → Re⟨O, L†_KMS O⟩_{ρβ} ≤ 0 for every O; reason: for a KMS-self-adjoint map, a nonpositive spectrum is equivalent to a nonpositive quadratic form (used so on p.28)
--   - encoding: L_x as the limit T → ∞ of L_{x,T} → integrals over ℝ and {s < t} ⊆ ℝ² directly; reason: the integrals converge absolutely since f_σ ∈ L¹; dominated convergence (p.26) gives the same matrices
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Proposition 3.4 (eqs. (3.26)–(3.27)), p.27

import Definitions.Def_SysBathGibbs_Coefficient

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Proposition 3.4 (KMS decomposition)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.27.
`Γ⁻¹ L_KMS Γ = L†_KMS`, and `L†_KMS` is KMS-self-adjoint and nonpositive; the same holds for each
`L_{KMS,x}`. Moreover `L(ρ) = L_KMS(ρ) - i[H_Lamb, ρ]`, `L_KMS(ρ_β) = 0`, `L(ρ_β) = -i[H_Lamb, ρ_β]`.

**Formalization Note.** "Nonpositive" is `Re ⟨O, L†_KMS O⟩_{ρ_β} ≤ 0` for all `O`; for a self-adjoint
map this is the statement on the spectrum used on p.28. -/
theorem proposition_3_4 :
    ∀ (β : ℝ), 0 < β → ∀ (n q : ℕ), 1 ≤ n → 1 ≤ q → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
      (∀ O, Gam β (chainHam h) (-1) (LKMS β h (Gam β (chainHam h) 1 O)) = hsAdjoint (LKMS β h) O) ∧
      IsKmsSelfAdjoint β (chainHam h) (hsAdjoint (LKMS β h)) ∧
      (∀ O, (kmsInner β (chainHam h) O (hsAdjoint (LKMS β h) O)).re ≤ 0) ∧
      (∀ x : Fin n,
        (∀ O, Gam β (chainHam h) (-1) (siteLKMS β h x (Gam β (chainHam h) 1 O)) =
          hsAdjoint (siteLKMS β h x) O) ∧
        IsKmsSelfAdjoint β (chainHam h) (hsAdjoint (siteLKMS β h x)) ∧
        ∀ O, (kmsInner β (chainHam h) O (hsAdjoint (siteLKMS β h x) O)).re ≤ 0) ∧
      (∀ ρ, Leff β h ρ = LKMS β h ρ + (-Complex.I) • comm (HLamb β h) ρ) ∧
      LKMS β h (gibbs β (chainHam h)) = 0 ∧
      Leff β h (gibbs β (chainHam h)) =
        (-Complex.I) • comm (HLamb β h) (gibbs β (chainHam h)) := by sorry

end SysBathGibbs
