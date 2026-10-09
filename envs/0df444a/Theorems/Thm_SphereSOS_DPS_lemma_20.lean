-- Prove2me | Theorems.Thm_SphereSOS_DPS_lemma_20
-- name    : SphereSOS.DPS.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:36.731931+00:00
-- url     : https://prove2.me/theorems/8eab44f2-d045-4300-aa64-cf5638a9aa92
-- title:
--   Lemma 20, p. 20 — ‖y‖^{2(ℓ−1)}p_M is csos iff ‖y‖^{2(ℓ−1)}p_M = (x ⊗ y^{⊗ℓ})†W(x ⊗ y^{⊗ℓ}) with W ⪰ 0
-- statement:
--   Let $M_{AB_1}$ be a Hermitian operator on $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$, $p_M(x,\bar x,y,\bar y)=\sum_{ijkl}M_{ij,kl}x_i\bar x_ky_j\bar y_l$, and let $\ell\ge1$ be an integer. Then $\|y\|^{2(\ell-1)}p_M$ is a complex sum of squares (csos) if and only if there exists a positive semidefinite operator $W_{AB[\ell]}\succeq0$ on $\mathcal H_A\otimes\mathcal H_B^{\otimes\ell}$ such that
--   $$\|y\|^{2(\ell-1)}p_M(x,\bar x,y,\bar y)=\big(x\otimes y^{\otimes\ell}\big)^\dagger W_{AB[\ell]}\big(x\otimes y^{\otimes\ell}\big)\qquad\forall x,y.\tag{61}$$
--
--   This is the analogue of Lemma 19 for the hierarchy $\mathcal{EXT}_\ell$ without partial-transpose constraints, and yields Theorem 12 (iii).
--
--   **Formalization Note** The level is $\ell=m+1$. As for Lemma 19, $p_M$ is taken literally from (25), and the set of right-hand sides is invariant under conjugating $(x,y)$, so the equivalence is the page's.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 20, Lemma 20, (61)

import Mathlib
import Definitions.Def_SphereSOS_DPS_Setting

namespace SphereSOS.DPS

open scoped ComplexOrder

/-- Lemma 20 (p. 20), with ℓ = m + 1: for Hermitian M, ‖y‖^{2(ℓ−1)} p_M is csos iff there is a PSD W
with ‖y‖^{2(ℓ−1)} p_M = (x ⊗ y^{⊗ℓ})† W (x ⊗ y^{⊗ℓ}) (61). -/
theorem lemma_20 {dA dB m : ℕ} (M : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hM : M.IsHermitian) :
    IsCSOS (fun x y => nsq y ^ m * pM M x y) ↔
      ∃ W : Matrix (Fin dA × (Fin (m + 1) → Fin dB)) (Fin dA × (Fin (m + 1) → Fin dB)) ℂ, W.PosSemidef ∧
        ∀ x y, nsq y ^ m * pM M x y = qf (tensVec 0 x y) W := by sorry

end SphereSOS.DPS
