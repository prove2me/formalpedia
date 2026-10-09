-- Prove2me | Theorems.Thm_SphereSOS_DPS_eq_37
-- name    : SphereSOS.DPS.eq_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:22.924472+00:00
-- url     : https://prove2.me/theorems/99e9d086-ad52-459e-b162-d5b2cca90fd9
-- title:
--   (37), pp. 16, 19 — (x ⊗ ȳ^{⊗s} ⊗ y^{⊗ℓ−s})†W(x ⊗ ȳ^{⊗s} ⊗ y^{⊗ℓ−s}) = (x ⊗ y^{⊗ℓ})†W^{T_{B[s]}}(x ⊗ y^{⊗ℓ})
-- statement:
--   Let $\ell\ge1$, $0\le s\le\ell$, and let $W$ be any matrix on $\mathcal H_A\otimes\mathcal H_{B_1}\otimes\cdots\otimes\mathcal H_{B_\ell}$, with $\mathcal H_A\simeq\mathbb C^{d_A}$ and each $\mathcal H_{B_i}\simeq\mathbb C^{d_B}$. Write $W^{\mathsf T_{B[s]}}$ for the partial transpose of $W$ on the first $s$ copies $B_1,\dots,B_s$. Then for all $x\in\mathbb C^{d_A}$ and $y\in\mathbb C^{d_B}$,
--   $$\big(x\otimes\bar y^{\otimes s}\otimes y^{\otimes\ell-s}\big)^\dagger W\big(x\otimes\bar y^{\otimes s}\otimes y^{\otimes\ell-s}\big)=\big(x\otimes y^{\otimes\ell}\big)^\dagger W^{\mathsf T_{B[s]}}\big(x\otimes y^{\otimes\ell}\big).$$
--
--   This is the identity $x^\dagger Zx=\bar x^\dagger Z^{\mathsf T}\bar x$ applied to the first $s$ factors; it turns (36) into (37) in Lemma 19 and is the only place where the partial transpose conditions of the DPS hierarchy enter the duality.
--
--   **Formalization Note** The level is $\ell=m+1$; the copies $B_1,\dots,B_\ell$ are coordinates $0,\dots,m$.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 16 (36)–(37), and p. 19, proof of Lemma 19 (restatement), first sentence

import Mathlib
import Definitions.Def_SphereSOS_DPS_Setting

namespace SphereSOS.DPS

open scoped ComplexOrder

/-- The rewriting of (36) into (37) (pp. 16, 19), via x†Zx = x̄†Zᵀx̄: for ℓ = m + 1 and
s ≤ ℓ, (x ⊗ ȳ^{⊗s} ⊗ y^{⊗(ℓ−s)})† W (x ⊗ ȳ^{⊗s} ⊗ y^{⊗(ℓ−s)}) = (x ⊗ y^{⊗ℓ})† W^{T_{B[s]}} (x ⊗ y^{⊗ℓ}). -/
theorem eq_37 {dA dB m : ℕ} (s : ℕ) (hs : s ≤ m + 1)
    (W : Matrix (Fin dA × (Fin (m + 1) → Fin dB)) (Fin dA × (Fin (m + 1) → Fin dB)) ℂ)
    (x : Fin dA → ℂ) (y : Fin dB → ℂ) :
    qf (tensVec s x y) W = qf (tensVec 0 x y) (ptB s W) := by sorry

end SphereSOS.DPS
