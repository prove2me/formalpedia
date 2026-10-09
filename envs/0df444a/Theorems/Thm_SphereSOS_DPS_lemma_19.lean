-- Prove2me | Theorems.Thm_SphereSOS_DPS_lemma_19
-- name    : SphereSOS.DPS.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:07.235275+00:00
-- url     : https://prove2.me/theorems/40060fda-7a8d-401e-a369-b9c5332580a6
-- title:
--   Lemma 19, p. 16 — ‖y‖^{2(ℓ−1)}p_M is rsos iff it equals Σ_{s=0}^ℓ (x ⊗ ȳ^{⊗s} ⊗ y^{⊗ℓ−s})†W_s(·) with W_s ⪰ 0
-- statement:
--   Let $M\in\mathrm{Herm}(d_Ad_B)$, let $p_M(x,\bar x,y,\bar y)=\sum_{ijkl}M_{ij,kl}x_i\bar x_ky_j\bar y_l$ and let $\ell\ge1$ be an integer. Then $\|y\|^{2(\ell-1)}p_M$ is a real sum of squares (rsos) if and only if there exist positive semidefinite operators $W_{s,AB[\ell]}\succeq 0$, $s=0,1,\dots,\ell$, on $\mathcal H_A\otimes\mathcal H_B^{\otimes\ell}$ such that, for all $x\in\mathbb C^{d_A}$, $y\in\mathbb C^{d_B}$,
--   $$\|y\|^{2(\ell-1)}p_M=\sum_{s=0}^{\ell}\big(x\otimes\bar y^{\otimes s}\otimes y^{\otimes\ell-s}\big)^\dagger W_{s,AB[\ell]}\big(x\otimes\bar y^{\otimes s}\otimes y^{\otimes\ell-s}\big)=\sum_{s=0}^{\ell}\big(x\otimes y^{\otimes\ell}\big)^\dagger W_{s,AB[\ell]}^{\mathsf T_{B[s]}}\big(x\otimes y^{\otimes\ell}\big).$$
--
--   This is the semidefinite characterization of the right-hand side of Theorem 12 (ii): it identifies rsos certificates of $\|y\|^{2(\ell-1)}p_M$ with the dual variables of the positivity and partial-transpose constraints of $\mathcal{DPS}_\ell$.
--
--   **Formalization Note** The level is $\ell=m+1$, $s$ ranges over `Fin (m + 2)`. With $p_M$ literally as in (25), $v^\dagger Wv$ on the tensor vectors equals the displayed form evaluated at $(\bar x,\bar y)$; the set of right-hand sides is invariant under that conjugation (replace $W_s$ by $\overline{W_s}$), so the equivalence is the page's. Both printed equalities (36) and (37) are kept.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 16, Lemma 19, (36)–(37); restated p. 19, (53)–(54)

import Mathlib
import Definitions.Def_SphereSOS_DPS_Setting

namespace SphereSOS.DPS

open scoped ComplexOrder

/-- Lemma 19 (pp. 16, 19), with ℓ = m + 1: for Hermitian M, ‖y‖^{2(ℓ−1)} p_M is rsos iff there are
PSD W_s, s = 0, …, ℓ, with ‖y‖^{2(ℓ−1)} p_M = ∑_s (x ⊗ ȳ^{⊗s} ⊗ y^{⊗(ℓ−s)})† W_s (x ⊗ ȳ^{⊗s} ⊗ y^{⊗(ℓ−s)})
(36) = ∑_s (x ⊗ y^{⊗ℓ})† W_s^{T_{B[s]}} (x ⊗ y^{⊗ℓ}) (37). -/
theorem lemma_19 {dA dB m : ℕ} (M : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hM : M.IsHermitian) :
    IsRSOS (fun x y => nsq y ^ m * pM M x y) ↔
      ∃ W : Fin (m + 2) → Matrix (Fin dA × (Fin (m + 1) → Fin dB)) (Fin dA × (Fin (m + 1) → Fin dB)) ℂ,
        (∀ s, (W s).PosSemidef) ∧
        (∀ x y, nsq y ^ m * pM M x y = ∑ s : Fin (m + 2), qf (tensVec (s : ℕ) x y) (W s)) ∧
        (∀ x y, nsq y ^ m * pM M x y =
          ∑ s : Fin (m + 2), qf (tensVec 0 x y) (ptB (s : ℕ) (W s))) := by sorry

end SphereSOS.DPS
