-- Prove2me | Theorems.Thm_UnitalMIP_theorem_5_3
-- name    : UnitalMIP.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:38.877699+00:00
-- url     : https://prove2.me/theorems/68414099-b8dc-46b9-a45d-5beff811ee08
-- title:
--   Theorem 5.3 — dimension-independent EPR weight $F_{m,\lambda}\ge\lambda^2$
-- statement:
--   Fix $0<\lambda\le1$. For every $m\ge1$ there are local quantum channels and a bipartite state $\zeta_{m,\lambda}$ such that
--
--   $$
--   \Psi_\lambda^{\otimes N_m}\longmapsto F_{m,\lambda}\Phi_d+(1-F_{m,\lambda})\zeta_{m,\lambda},\qquad d=2^m,\quad N_m=2^m-1+2m,
--   $$
--
--   where
--
--   $$
--   F_{m,\lambda}=\frac{d+2(d-1)\lambda+(d-1)(d-2)\lambda^2}{d^2}\ge\lambda^2 .
--   $$
--
--   Every entangled boundary state thus contains, in every dimension, an exact maximally entangled component whose weight does not degrade with the number of EPR pairs; this drives the RE lower bound.
--
--   **Formalization Note** $\Phi_d$ is the state of $m$ EPR pairs on $(\mathbb C^2)^{\otimes m}\otimes(\mathbb C^2)^{\otimes m}$; channels are finite normalized Kraus families (the published `IsChannel`), and $\Lambda_A\otimes\Lambda_B$ is the published `ShorEBAdditivity.tensorChannel`.
--
--   Differences from the source:
--   - reading: “local quantum channels” mapping $\Psi_\lambda^{\otimes N_m}$ → a product $\Lambda_A\otimes\Lambda_B$ of quantum channels, each from one party's $N_m$ qubits to $m$ qubits; reason: local operations without communication; the shared randomness of the twirl comes from measuring extra copies of $\Psi_\lambda$, which are part of the input (p.72)
--   - encoding: $\psi^{\otimes n}$ → `tensorPow ψ n`: the same operator with Alice's $n$ registers collected first; reason: a permutation of tensor factors; Alice holds the first qubit of every copy, as in the source
--   - generalization: the §1.1 standing assumption (“Throughout, let ψ be a fixed two-qubit state … and assume that its entries are computable in polynomial time”, p.4) → every real $\lambda\in(0,1]$, no computability hypothesis on $\Psi_\lambda$; reason: the conversion is a statement about states and channels; it specializes to the source's claim on every computable $\lambda$
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Theorem 5.3, p.72

import Mathlib
import Definitions.Def_UnitalMIP_omegaInf
import Definitions.Def_UnitalMIP_canonicalState
import Definitions.Def_ShorEBAdditivity_tensorChannel

open scoped Matrix

namespace UnitalMIP

/-- **Theorem 5.3** (Dimension-independent EPR weight; Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), p.72). Fix `0 < λ ≤ 1`. For every
`m ≥ 1` there are local quantum channels and a bipartite state `ζ_{m,λ}` such that
`Ψ_λ^{⊗N_m} ↦ F_{m,λ} Φ_d + (1 − F_{m,λ}) ζ_{m,λ}`, `d = 2^m`, `N_m = 2^m − 1 + 2m`, where
`F_{m,λ} = (d + 2(d − 1)λ + (d − 1)(d − 2)λ²)/d² ≥ λ²` (58).

**Formalization Note** The local channels are a product `Λ_A ⊗ Λ_B` (the published `ShorEBAdditivity.tensorChannel`) of quantum
channels (the published `QAlgorithms.IsChannel`: a finite normalized Kraus family) from each party's
`N_m` qubits to `m` qubits. `Ψ_λ^{⊗N_m}` is regrouped (`tensorPow`): Alice holds the first qubit of
every copy. `Φ_d` is `maxEnt (Fin m → Fin 2)` (`m` EPR pairs). Both clauses of (58) are stated. -/
theorem theorem_5_3 (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (m : ℕ) (hm : 1 ≤ m) :
    let d : ℝ := (2 : ℝ) ^ m
    let F : ℝ := (d + 2 * (d - 1) * lam + (d - 1) * (d - 2) * lam ^ 2) / d ^ 2
    ∃ (ΛA : QAlgorithms.Superop (Fin (2 ^ m - 1 + 2 * m) → Fin 2) (Fin m → Fin 2))
      (ΛB : QAlgorithms.Superop (Fin (2 ^ m - 1 + 2 * m) → Fin 2) (Fin m → Fin 2))
      (ζ : Matrix ((Fin m → Fin 2) × (Fin m → Fin 2)) ((Fin m → Fin 2) × (Fin m → Fin 2)) ℂ),
      QAlgorithms.IsChannel ΛA ∧ QAlgorithms.IsChannel ΛB ∧ QAlgorithms.IsDensityMatrix ζ ∧
      ShorEBAdditivity.tensorChannel ΛA ΛB (tensorPow (PsiBoundary lam) (2 ^ m - 1 + 2 * m)) =
        (F : ℂ) • maxEnt (Fin m → Fin 2) + ((1 - F : ℝ) : ℂ) • ζ ∧
      lam ^ 2 ≤ F := by sorry

end UnitalMIP
