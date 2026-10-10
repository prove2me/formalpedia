-- Prove2me | Theorems.Thm_QCQPTightness_MultTight_objective_direction_zero
-- name    : QCQPTightness.MultTight.objective_direction_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:05.708729+00:00
-- url     : https://prove2.me/theorems/9d9129d7-05ad-4e13-b312-029b7c670b2f
-- title:
--   App. B, proof of Theorem 8, p. 36 — on 𝒟_SDP ∩ H, minimality of t̂ forces ⟨A_0x̂ + b_0, y ⊗ z⟩ = 0
-- statement:
--   Let the QCQP have an explicit representation $A_i = I_k\otimes\mathbb A_i$ ($i\in[\![0,m]\!]$), $N = kn$, and let $H=\{(x,t):2t=\mathrm{Opt}_{\mathrm{SDP}}\}$. Suppose
--
--   1. $(\hat x,\hat t)\in\mathcal D_{\mathrm{SDP}}\cap H$ and $(\hat x,\hat t,Z)$ satisfies (19);
--   2. $Z = zz^\top + Z'$ with $z\in\mathbb R^n$ and $Z'\succeq 0$;
--   3. $y\in\mathbf S^{k-1}$ satisfies $\langle A_i\hat x+b_i,\ y\otimes z\rangle = 0$ for all $i\in[\![m]\!]$ (system (20)).
--
--   Then
--
--   $$\langle A_0\hat x+b_0,\ y\otimes z\rangle = 0 .$$
--
--   In the proof of Theorem 8 this is what lets the objective constraint of (19) survive the move $(\hat x,\hat t,Z)\mapsto(\hat x\pm y\otimes z,\hat t,Z-zz^\top)$: the two moved points lie in $\mathcal D_{\mathrm{SDP}}$ at heights $\hat t\pm\langle A_0\hat x+b_0,y\otimes z\rangle$, and $\hat t$ is minimal there.
--
--   **Formalization Note** Assumption 1 and the standing assumption $m\ge 1$ are not needed and are dropped. The decomposition of $Z$ is a hypothesis, as in the proof, where $z$ is the first term of a rank-one decomposition of $Z$.
-- source:
--   arXiv:1911.09195v3, App. B, proof of Theorem 8, p. 36

import Mathlib
import Definitions.Def_QCQPTightness_MultTight_QCQP
import Definitions.Def_QCQPTightness_MultTight_Mult
import Definitions.Def_QCQPTightness_MultTight_Kron

namespace QCQPTightness.MultTight

open QCQP Matrix

/-- App. B, proof of Theorem 8 (arXiv:1911.09195v3, p. 36): let `(x̂, t̂) ∈ 𝒟_SDP ∩ H` with
`(x̂, t̂, Z)` satisfying (19), `Z = zzᵀ + Z'` with `Z' ⪰ 0`, and `y ∈ 𝐒^{k−1}` solving (20).
Then `⟨A₀x̂ + b₀, y ⊗ z⟩ = 0`. -/
theorem objective_direction_zero {N m : ℕ} (P : QCQP N m)
    {k n : ℕ} (h : k * n = N) (𝔸₀ : Matrix (Fin n) (Fin n) ℝ)
    (𝔸 : Fin m → Matrix (Fin n) (Fin n) ℝ) (hrep : P.IsKronRep h 𝔸₀ 𝔸)
    (p : (Fin N → ℝ) × ℝ) (hp : p ∈ P.DSDP ∩ P.hyperplaneH)
    (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : P.IsDualCert19 h 𝔸₀ 𝔸 p.1 p.2 Z)
    (z : Fin n → ℝ) (Z' : Matrix (Fin n) (Fin n) ℝ) (hZ' : Z'.PosSemidef)
    (hdec : Z = Matrix.vecMulVec z z + Z')
    (y : Fin k → ℝ) (hy : y ⬝ᵥ y = 1)
    (h20 : ∀ i, (P.A i *ᵥ p.1 + P.b i) ⬝ᵥ kronVec h y z = 0) :
    (P.A₀ *ᵥ p.1 + P.b₀) ⬝ᵥ kronVec h y z = 0 := by sorry

end QCQPTightness.MultTight
