-- Prove2me | Theorems.Thm_SysBathGibbs_proposition_6_5
-- name    : SysBathGibbs.proposition_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:02.542299+00:00
-- url     : https://prove2.me/theorems/df205164-ded8-449d-8683-c04a57bd1270
-- title:
--   Proposition 6.5 — Estimates for spectral conditional expectations
-- statement:
--   There are $C,c>0$, depending only on $\beta$ and $q$ ($\sigma=\beta/2$), such that for every chain (1.2) on $n\ge1$ sites and every interval $I\subseteq[n]$, with $p_I$ the spectral conditional expectation:
--
--   1. (Conditional variance.) For every $O$, $\|(\mathrm{id}-p_I)O\|^2_{\rho_\beta}\le C\sum_{y\in I,a}\|[P_{y,a},O]\|^2_{\rho_\beta}$.
--   2. (Local approximants.) For every $r\ge0$ there is $p_I^r\in\mathcal A(N_r(I))$ with $\|p_I-p_I^r\|_{\rho_\beta\to\rho_\beta}\le Ce^{-cr}$ and $\|p_I^r\|_{\rho_\beta\to\rho_\beta}\le1$.
--   3. (Trivializing a Gibbs-centered island.) If $\mathcal A^\star=\mathcal A\in\mathcal A(S)$ for $S\subseteq I$ with $\operatorname{dist}(S,I^c)\ge R$, then
--   $$
--   \|p_I\mathcal Ap_I-\langle\mathbf 1,\mathcal A(\mathbf 1)\rangle_{\rho_\beta}p_I\|_{\rho_\beta\to\rho_\beta}\le C(1+|S|)e^{-cR}\|\mathcal A\|_{\rho_\beta\to\rho_\beta}.
--   $$
--
--   Consequently, for all $C_0,c_0>0$ there are $C,c>0$ (depending on $\beta,q,C_0,c_0$) such that for every uniformly coefficient-quasi-local family $(\mathcal A_x)$ with constants $C_0,c_0$, $\mathcal A_x^\star=\mathcal A_x$ and $\langle\mathbf 1,\mathcal A_x(\mathbf 1)\rangle_{\rho_\beta}=0$, all $x$ and $r\ge0$: $\|p_{N_r(x)}\mathcal A_xp_{N_r(x)}\|_{\rho_\beta\to\rho_\beta}\le Ce^{-cr}$.
--
--   Differences from the source:
--   - encoding: σ a free parameter of (1.4)–(1.8) → σ = β/2 throughout; reason: the paper fixes σ = β/2 throughout (p.10); no other width is stated
--   - encoding: a chain [n] of qudits of dimension 2^q → n ≥ 1 and q ≥ 1 as hypotheses; reason: a chain has a site and a qudit has q ≥ 1 qubits; Q = 4^q − 1 ≥ 1 is used throughout
--   - generalization: "every interval I ⊆ [n]" → every order-connected I ⊆ Fin n, including ∅ (where p_∅ = id); reason: every interval is order-connected, so the statement specializes to the source on nonempty intervals; at I = ∅ all three bounds hold trivially
--   - encoding: dist(S, I^c) ≥ R → R ≤ |y − z| for all y ∉ I, z ∈ S; reason: the distance to an empty set is +∞, matching the vacuous pointwise form
--   - encoding: the projection p_I → any map with the characterizing property of Definition 6.1; reason: the property determines the orthogonal projection uniquely
--   - encoding: the maps A_x of (6.5) → ℂ-linear maps on matrices; reason: the superoperators of the paper are linear; (6.5) forces A_x to agree with a linear map on all O ≠ 0
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Proposition 6.5 (eqs. (6.6)–(6.9)), p.47

import Definitions.Def_SysBathGibbs_Coefficient

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Proposition 6.5 (Estimates for spectral conditional expectations)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.47.
There are `C, c > 0`, depending only on `β, q`, such that for every `n` and every interval `I ⊆ [n]`:
(i) `‖(id - p_I)O‖² ≤ C ∑_{y∈I,a} ‖[P_{y,a}, O]‖²`; (ii) for every `r ≥ 0` there is `p^r_I ∈ A(N_r(I))` with
`‖p_I - p^r_I‖ ≤ C e^{-cr}`, `‖p^r_I‖ ≤ 1`; (iii) if `A⋆ = A ∈ A(S)`, `S ⊆ I`, `dist(S, Iᶜ) ≥ R`, then
`‖p_I A p_I - ⟨1, A(1)⟩ p_I‖ ≤ C(1 + |S|) e^{-cR} ‖A‖`. Consequently, (6.9), for a uniformly
coefficient-quasi-local family with `A_x⋆ = A_x`, `⟨1, A_x(1)⟩ = 0`: `‖p_{N_r(x)} A_x p_{N_r(x)}‖ ≤ C e^{-cr}`,
with `C, c` depending only on `β, q` and the constants in (6.5).

**Formalization Note.** An interval is an order-connected subset of `Fin n`; the empty set is one, with
`p_∅ = id`. "`dist(S, Iᶜ) ≥ R`" is `R ≤ |y - z|` for `y ∉ I`, `z ∈ S`, so it holds for every `R` when
`Iᶜ` or `S` is empty (`dist` to the empty set is `+∞`). `p_I` is any map satisfying `IsSpectralCE`; there
is exactly one. -/
theorem proposition_6_5 :
    ∀ (β : ℝ), 0 < β → ∀ q : ℕ, 1 ≤ q →
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
          ∀ (I : Set (Fin n)), I.OrdConnected →
            ∀ p : SysMat n q → SysMat n q, IsSpectralCE β (chainHam h) I p →
              (∀ O : SysMat n q,
                kmsNorm β (chainHam h) (O - p O) ^ 2 ≤
                  C * ∑ y : Fin n, ∑ a : Coupling q,
                    Set.indicator I
                      (fun y => kmsNorm β (chainHam h) (comm (pauliString y a.1) O) ^ 2) y) ∧
              (∀ r : ℝ, 0 ≤ r →
                ∃ pr ∈ coefLocal β (chainHam h) (nbhd r I),
                  kmsOpNorm β (chainHam h) (p - pr) ≤ ENNReal.ofReal (C * Real.exp (-c * r)) ∧
                  kmsOpNorm β (chainHam h) pr ≤ 1) ∧
              ∀ (S : Set (Fin n)) (R : ℝ), S ⊆ I →
                (∀ y, y ∉ I → ∀ z ∈ S, R ≤ |(y.val : ℝ) - (z.val : ℝ)|) →
                ∀ A ∈ coefLocal β (chainHam h) S, IsKmsSelfAdjoint β (chainHam h) A →
                  kmsOpNorm β (chainHam h)
                      (fun O => p (A (p O)) -
                        kmsInner β (chainHam h) 1 (A 1) • p O) ≤
                    ENNReal.ofReal (C * (1 + (S.ncard : ℝ)) * Real.exp (-c * R)) *
                      kmsOpNorm β (chainHam h) A) ∧
      ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ →
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ (n : ℕ), 1 ≤ n → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
            ∀ A : Fin n → (SysMat n q →ₗ[ℂ] SysMat n q),
              IsCoefQuasiLocal β (chainHam h) C₀ c₀ (fun x => A x) →
              (∀ x, IsKmsSelfAdjoint β (chainHam h) (A x)) →
              (∀ x, kmsInner β (chainHam h) 1 (A x 1) = 0) →
              ∀ (x : Fin n) (r : ℝ), 0 ≤ r →
                ∀ p : SysMat n q → SysMat n q,
                  IsSpectralCE β (chainHam h) (nbhd r {x}) p →
                  kmsOpNorm β (chainHam h) (fun O => p (A x (p O))) ≤
                    ENNReal.ofReal (C * Real.exp (-c * r)) := by sorry

end SysBathGibbs
