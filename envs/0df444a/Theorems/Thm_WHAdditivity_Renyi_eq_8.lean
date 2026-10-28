-- Prove2me | Theorems.Thm_WHAdditivity_Renyi_eq_8
-- name    : WHAdditivity.Renyi.eq_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:25:55.594226+00:00
-- url     : https://prove2.me/theorems/1ab30cd2-f873-4f38-9f8c-36398e415836
-- title:
--   (8), pp. 3–4 — Tr X_N(Ω)² = ∏ⱼ 1/(dⱼ−1)² Σ_Λ Tr ρ²_Λ ∏_{j∈Λᶜ}(dⱼ−2) ≤ ∏ⱼ 1/(dⱼ−1)
-- statement:
--   Let $N\in\mathbb N$, $d_1,\dots,d_N\ge 2$, and let $\Omega\in\bigotimes_{j=1}^N\mathbb C^{d_j}$ be a unit vector. Put $X = X_N(\Omega) = \bigotimes_j\Gamma_{d_j}(|\Omega\rangle\langle\Omega|)$, the output of the product of Werner–Holevo channels, and let $\rho_\Lambda$ be the reduced matrix of $|\bar\Omega\rangle\langle\bar\Omega|$ on the sites in $\Lambda\subset\{1,\dots,N\}$, with $\Lambda^{\mathrm c}$ the complement in $\{1,\dots,N\}$. Then every line of the computation (8) holds:
--
--   $$\begin{aligned}\operatorname{Tr}X^2 &= \prod_{j=1}^N\frac{1}{(d_j-1)^2}\sum_{\Lambda,\Lambda'}(-1)^{|\Lambda|+|\Lambda'|}\operatorname{Tr}\bigl((\rho_\Lambda\otimes\mathbb 1_{\Lambda^{\mathrm c}})(\rho_{\Lambda'}\otimes\mathbb 1_{\Lambda'^{\mathrm c}})\bigr)\\ &= \prod_{j=1}^N\frac{1}{(d_j-1)^2}\sum_{\Lambda,\Lambda'}(-1)^{|\Lambda|+|\Lambda'|}\Bigl(\prod_{j\in(\Lambda\cup\Lambda')^{\mathrm c}}d_j\Bigr)\operatorname{Tr}\rho_{\Lambda\cap\Lambda'}^2\\ &= \prod_{j=1}^N\frac{1}{(d_j-1)^2}\sum_{\Lambda}\operatorname{Tr}\rho_\Lambda^2\sum_{\Delta\subset\Lambda^{\mathrm c}}(-1)^{|\Delta|}\sum_{\Delta'\subset\Lambda^{\mathrm c}\setminus\Delta}(-1)^{|\Delta'|}\prod_{j\in(\Lambda^{\mathrm c}\setminus\Delta)\setminus\Delta'}d_j\\ &= \prod_{j=1}^N\frac{1}{(d_j-1)^2}\sum_{\Lambda}\operatorname{Tr}\rho_\Lambda^2\prod_{j\in\Lambda^{\mathrm c}}(d_j-2)\ \le\ \prod_{j=1}^N\frac{1}{d_j-1},\end{aligned}$$
--
--   where all sums run over subsets of $\{1,\dots,N\}$; in particular $\operatorname{Tr}X^2$ is real.
--
--   The bound says that the purity of the output of $\bigotimes_j\Gamma_{d_j}$ on any pure input, entangled or not, is at most the purity $\prod_j 1/(d_j-1)$ of a product output; it is the inequality from which the paper derives the lower bound in (7).
--
--   **Formalization Note.** $\operatorname{Tr}X^2$ is `(X * X).trace`, a complex number; the statement asserts its imaginary part is $0$ and bounds its real part. $\bar\Omega$ is `star Ω`. The subsets $\Delta,\Delta'$ range over `Finset.powerset`.
--
--   Differences from the source:
--   - encoding: Γ_{d_j} with 1/(d_j − 1) → hypotheses 2 ≤ d_j; reason: (6) is undefined at d_j = 1.
--   - encoding: ⊗_j Γ_{d_j} → the linear extension of (6), tensored through matrix units; reason: needed for entangled inputs; agrees with (6) on density matrices.
--   - encoding: a real trace compared with ≤ → the complex trace has imaginary part 0, and its real part is bounded; reason: the inequality in the paper presupposes that Tr X² is real; Lean states it.
--   - encoding: sites 1, …, N → sites `Fin N` from 0; reason: relabelling only.
--   - generalization: N ≥ 1 implicitly → every N ∈ ℕ; reason: N = 0 is the trivial case (Tr X² = 1 = empty product); specializes to the paper's N ≥ 1.
-- source:
--   Alicki, Fannes, Note on multiple additivity of minimal Renyi entropy output of the Werner–Holevo channels, arXiv:quant-ph/0407033v2, pp. 3–4, (8)

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace WHAdditivity.Renyi

theorem eq_8 (N : ℕ) (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (Ω : Config d → ℂ)
    (hΩ : IsUnitVector Ω) :
    let X := tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω)
    let ρ := pureState (star Ω)
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N), ∑ Λ' : Finset (Fin N),
          (-1 : ℂ) ^ (Λ.card + Λ'.card) *
            (tensorIdentity d Λ (reducedMatrix d Λ ρ) *
              tensorIdentity d Λ' (reducedMatrix d Λ' ρ)).trace ∧
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N), ∑ Λ' : Finset (Fin N),
          (-1 : ℂ) ^ (Λ.card + Λ'.card) *
            ((∏ j ∈ (Λ ∪ Λ')ᶜ, (d j : ℂ)) * (reducedMatrix d (Λ ∩ Λ') ρ ^ 2).trace) ∧
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N),
          (reducedMatrix d Λ ρ ^ 2).trace *
            ∑ Δ ∈ Λᶜ.powerset, (-1 : ℂ) ^ Δ.card *
              ∑ Δ' ∈ (Λᶜ \ Δ).powerset, (-1 : ℂ) ^ Δ'.card *
                ∏ j ∈ (Λᶜ \ Δ) \ Δ', (d j : ℂ) ∧
    (X * X).trace =
        (∏ j, (((d j : ℂ) - 1) ^ 2)⁻¹) * ∑ Λ : Finset (Fin N),
          (reducedMatrix d Λ ρ ^ 2).trace * ∏ j ∈ Λᶜ, ((d j : ℂ) - 2) ∧
    (X * X).trace.im = 0 ∧
    (X * X).trace.re ≤ ∏ j, ((d j : ℝ) - 1)⁻¹ := by sorry

end WHAdditivity.Renyi
