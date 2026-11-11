-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_proposition_8_1
-- name    : RandProdExp.TwoSided.proposition_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:21:17.836345+00:00
-- url     : https://prove2.me/theorems/d1132722-cd6a-472c-9444-3d8616d4d8f4
-- title:
--   Proposition 8.1 — $\mathbb E\max_\lambda\|T_\lambda\|_{\mathrm{op}}\le2(4/\rho)^q\sqrt\eta$ for $\eta$-sparse restrictions of $\bigotimes_jD_j$
-- statement:
--   In the setup of §8, let $D>0$, $q\ge1$, $\nu\ge0$ with $\nu+q\le D$, $\rho\in(0,1)$, and integers $k_j\in[n]$ with $k_j\ge\rho n$ for $j\in[q]$; let $G_j=k_j^{-1/2}\sigma^{(j)}$ be normalized Rademacher matrices with independent uniform signs and $D_j=G_j^\top G_j-\mathrm{Id}_{\mathbb R^n}$. Let $\Lambda$ be a finite indexing set with $|\Lambda|\le n^\nu$ and, for $\lambda\in\Lambda$, let $X_\lambda,Y_\lambda\subseteq[n]^q$ be $\eta$-sparse for some $\eta\in(0,1)$, fixed independently of the signs. With $T_\lambda=\Pi_{X_\lambda}(\bigotimes_{j=1}^qD_j)\iota_{Y_\lambda}:\mathbb R^{Y_\lambda}\to\mathbb R^{X_\lambda}$, for
--   $n\ge N_{D,q,\eta}=\max\{16(192D/e)^{24},\eta^{-2/q}\}$,
--   $$\mathbb E_\sigma\Big[\max_{\lambda\in\Lambda}\|T_\lambda\|_{\mathrm{op}}\Big]\le2\Big(\frac4\rho\Big)^q\sqrt\eta ,$$
--   and if $\Lambda=\emptyset$ this expectation is $0$. It bounds the sparse factor in the decomposition of the plane-interaction matrix.
--
--   Differences from the source:
--   - encoding: §8 setup: k_i ∈ [n], k_i ≥ ρn for i ∈ [D], of which G_1, …, G_q are used → k : Fin q → ℕ with 1 ≤ k_j ≤ n and ρn ≤ k_j; reason: only the q matrices that enter T_λ matter
--   - encoding: Λ a fixed (finite) indexing set; max over Λ, which is 0 when Λ = ∅ → Λ : Type with [Fintype Λ]; the maximum as the real iSup over Λ (0 for empty Λ); reason: the iSup of finitely many reals is their maximum; |Λ| ≤ n^ν forces finiteness
--   - encoding: X_λ, Y_λ ⊆ [n]^q → Finsets of Fin q → Fin n; reason: finite sets; the matrix T_λ is indexed by their elements
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 55, Proposition 8.1 (= Proposition 7.11, p. 49)

import Mathlib
import Definitions.Def_RandProdExp_TwoSided_Grid
import Definitions.Def_RandProdExp_TwoSided_RealModel
import Definitions.Def_RandProdExp_TwoSided_Params

namespace RandProdExp.TwoSided

/-- **Proposition 8.1** (Proposition 7.11 restated, p. 55). In the setup of §8 (`D > 0`, `q ≥ 1`,
`ν ≥ 0`, `ν + q ≤ D`, `ρ ∈ (0, 1)`, `k_j ∈ [n]` with `k_j ≥ ρ n`, `G_j` normalized Rademacher,
`D_j = G_jᵀ G_j − Id`), let `Λ` be an indexing set with `|Λ| ≤ n^ν` and, for `λ ∈ Λ`, let
`X_λ, Y_λ ⊆ [n]^q` be η-sparse (`η ∈ (0, 1)`), fixed independently of the signs. With
`T_λ = Π_{X_λ} (⊗_{j=1}^q D_j) ι_{Y_λ}`, for `n ≥ N_{D,q,η} = max{16 (192 D / e)^{24}, η^{−2/q}}`,
`E[max_{λ ∈ Λ} ‖T_λ‖_op] ≤ 2 (4/ρ)^q √η`; if `Λ = ∅` this expectation is `0`. -/
theorem proposition_8_1 (D q ν : ℕ) (hD : 0 < D) (hq : 1 ≤ q) (hqν : ν + q ≤ D)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (n : ℕ) (k : Fin q → ℕ)
    (hk : ∀ j, 1 ≤ k j ∧ k j ≤ n ∧ ρ * n ≤ k j)
    (Λ : Type) [Fintype Λ] (hΛ : Fintype.card Λ ≤ n ^ ν)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (X Y : Λ → Finset (Fin q → Fin n))
    (hX : ∀ l, IsEpsSparse η (X l : Set (Fin q → Fin n)))
    (hY : ∀ l, IsEpsSparse η (Y l : Set (Fin q → Fin n)))
    (hn : NDqEta D q η ≤ n) :
    signAvg (fun σ : (j : Fin q) → Matrix (Fin (k j)) (Fin n) ℤˣ =>
        ⨆ l : Λ, opNorm (sparseBlock σ (X l) (Y l))) ≤ 2 * (4 / ρ) ^ q * Real.sqrt η ∧
      (IsEmpty Λ → signAvg (fun σ : (j : Fin q) → Matrix (Fin (k j)) (Fin n) ℤˣ =>
        ⨆ l : Λ, opNorm (sparseBlock σ (X l) (Y l))) = 0) := by sorry

end RandProdExp.TwoSided
