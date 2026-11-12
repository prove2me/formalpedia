-- Prove2me | Theorems.Thm_TorchFire_Model_lemma_8_2
-- name    : TorchFire.Model.lemma_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:38:30.564278+00:00
-- url     : https://prove2.me/theorems/828d2edd-0be8-43b8-8dcd-4227b9927511
-- title:
--   Lemma 8.2 — extraction from $N$ separated computations on an entangled input (72)
-- statement:
--   Fix an integer $\beta\ge1$ and $N$ locations. At location $i$ consider the original and modified $q$-query computations (63)
--   $$U^1_i=G_{i,q}O^1_{i,q}\cdots G_{i,1}O^1_{i,1}G_{i,0},\qquad U^0_i=G_{i,q}O^0_{i,q}\cdots G_{i,1}O^0_{i,1}G_{i,0}$$
--   on $H_i\otimes W_i$, with acceptance projector $\Pi_i$, accepting maps $A_i=\Pi_iU^1_iJ_i$, $C_i=\Pi_iU^0_iJ_i$ (64), and a computational-basis diagonal witness projector $Q_i$ with $(O^1_{i,j}-O^0_{i,j})(I-Q_i)=0$ for every $j$ (65). Let $\rho$ be a possibly subnormalized joint state on $\bigotimes_iH_i$, $\rho_i$ its reduced states, $E_i,L_i$ the witness-sampler effect (69) and filter (70), and $\varepsilon_\beta=\sum_i\mathrm{Tr}(C_iL_i\rho_iL_iC_i^\dagger)$ (71).
--
--   Let $X_i$ indicate acceptance by the original computation at location $i$. For every $\delta\in(0,1)$ the local extracting procedure of step 4 (p.63) — which receives only its local input and fresh workspace, uses only $U^0_{i,<j}$, $(U^0_{i,<j})^\dagger$ and $Q_i$, and makes one initial witness test and at most $t=\lceil2\beta/\delta^2\rceil$ further rounds — outputs a witness or a failure; let $Y_i$ indicate a witness output. Then for every $d\in[N]$,
--   $$\Pr\Big[\sum_iX_i\ge d\Big]\le\Pr\Big[\sum_iY_i\ge d\Big]+N\delta(2+\delta)+(1+\delta^{-1})\Big(2\varepsilon_\beta+\frac{8Nq^2}{2\beta+1}\Big)\quad(72).$$
--   The two probabilities refer to separate executions on the same input $\rho$; they are $\mathrm{Tr}(T_d(A_1^\dagger A_1,\dots,A_N^\dagger A_N)\rho)$ and $\mathrm{Tr}(T_d(W_1,\dots,W_N)\rho)$ with the threshold effect (83) and $W_i$ the extractor's success effect.
--
--   The lemma converts simultaneous acceptance at several non-communicating locations into simultaneous witness extraction, even when the locations share entanglement; it is the core of the non-proliferation proof.
--
--   Differences from the source:
--   - reading: Q_i "on the input register (i.e. on H_i)" → Q_i a computational-basis diagonal projector on H_i ⊗ W_i; reason: paper.md decision 12: (65) multiplies Q_i with operators on H_i ⊗ W_i, and the proof applies it as Q V_j
--   - reading: "there are local extracting procedures that output a witness or a failure" → the explicit step-4 procedure; W_i is its success effect; reason: paper.md decision 14: read literally the existence claim is trivial (output a fixed witness)
--   - reading: ε_β (71), printed as Tr(L_i C_i† ρ_i C_i L_i) in (90) → ε_β = Σ_i Tr(C_i L_i ρ_i L_i C_i†) (71); reason: paper.md decision 13: (90) does not type-check
--   - generalization: expectations over the classical oracles in ε_β and the two probabilities → the inequality at fixed unitaries and a fixed state ρ; reason: the expectation follows by linearity
--   - encoding: a q-query computation with the sampler choosing j ∈ [q] uniformly → q ≥ 1; reason: excludes only q = 0, where the sampler is undefined
--   - encoding: Pr[Σ X_i ≥ d], Pr[Σ Y_i ≥ d] → Tr(T_d(A_i†A_i)ρ), Tr(T_d(W_i)ρ); reason: (83): the local tests act on disjoint registers
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Lemma 8.2, (72), p.61; setting (63)–(71) pp.59–60; extractor §8.1 step 4 p.63

import Mathlib
import Definitions.Def_TorchFire_Model_LocalComp

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix

namespace TorchFire.Model

/-- **Lemma 8.2** (extraction from separated computations), p.61 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593), with the setting (63)–(71) of
pp.59–60. Fix an integer `β ≥ 1` and `N` locations; at location `i` the original and modified
`q`-query computations `U^1_i`, `U^0_i` (63) act on `H_i ⊗ W_i` with common unitaries `G_{i,j}` and
query unitaries `O^1_{i,j}`, `O^0_{i,j}` that agree outside the witness projector `Q_i` (65); `Π_i` is
the acceptance projector and `A_i = Π_i U^1_i J_i` (64). Let `ρ` be a possibly subnormalized state on
`⨂_i H_i`. Let `X_i` indicate acceptance by the original computation at location `i`, and `Y_i` a
successful witness output of the local extractor of step 4 (p.63) with parameters `β, δ` (effect `W_i`).
Then for every `δ ∈ (0, 1)` and every `d ∈ [N]`,
`Pr[Σ_i X_i ≥ d] ≤ Pr[Σ_i Y_i ≥ d] + Nδ(2 + δ) + (1 + δ^{−1})(2ε_β + 8Nq²/(2β + 1))` (72),
where `Pr[Σ_i X_i ≥ d] = Tr(T_d(A_1†A_1, …, A_N†A_N) ρ)`, `Pr[Σ_i Y_i ≥ d] = Tr(T_d(W_1, …, W_N) ρ)` (83),
and `ε_β = Σ_i Tr(C_i L_i ρ_i L_i C_i†)` (71). Stated at fixed unitaries; the expectation over the oracles
follows by linearity. -/
theorem lemma_8_2 {N : ℕ} {H : Fin N → Type} [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    (C : (i : Fin N) → LocalComp (H i)) (q β : ℕ) (hq : 1 ≤ q) (hβ : 1 ≤ β)
    (hG : ∀ i, ∀ j ≤ q, (C i).G j ∈ Matrix.unitaryGroup (H i × (C i).W) ℂ)
    (hO : ∀ i, ∀ j < q, (C i).O1 j ∈ Matrix.unitaryGroup (H i × (C i).W) ℂ ∧
      (C i).O0 j ∈ Matrix.unitaryGroup (H i × (C i).W) ℂ)
    (hPi : ∀ i, (C i).Pi.IsHermitian ∧ (C i).Pi * (C i).Pi = (C i).Pi)
    (hwit : ∀ i, ∀ j < q, ((C i).O1 j - (C i).O0 j) * (1 - (C i).Qmat) = 0)
    (ρ : Matrix ((i : Fin N) → H i) ((i : Fin N) → H i) ℂ) (hρ : IsSubState ρ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (d : ℕ) (hd1 : 1 ≤ d) (hdN : d ≤ N) :
    accProb (thresholdEffect d fun i => ((C i).Amap q)ᴴ * (C i).Amap q) ρ ≤
      accProb (thresholdEffect d fun i => (C i).extractorEffect q β δ) ρ + N * δ * (2 + δ) +
        (1 + δ⁻¹) * (2 * epsBeta C q β ρ + 8 * N * (q : ℝ) ^ 2 / (2 * β + 1)) := by sorry

end TorchFire.Model
