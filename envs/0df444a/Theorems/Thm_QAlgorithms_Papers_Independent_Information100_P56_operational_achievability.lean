-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_operational_achievability
-- name    : QAlgorithms.Papers.Independent.Information100.P56.operational_achievability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:19:40.111666+00:00
-- url     : https://prove2.me/theorems/ba902d76-75ae-4e06-a8de-9d5ad3620941
-- title:
--   Theorem V.3: operational achievability and deterministic seeds
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. Let $G$ be a finite group. For $R=B,E$, let $U_R$ be a possibly projective unitary representation and $W_R(g)=U_R(g)\rho_RU_R(g)^\dagger$ for a density seed $\rho_R$. Write $\rho_R(P)=\sum_gP(g)W_R(g)$ and $\Delta(P)=H(\rho_B(P))-H(\rho_E(P))$. A code of length $N\ge1$ maps a uniform index in a set of size $K=ML$ to a word in $G^N$. A finite nonempty balanced universal$_2$ family hashes these indices onto $M$ messages, with every fiber of size $L\ge1$. Its public seed is independent and uniform. To send a uniform secret message, draw uniformly within its hash fiber and independently randomize each channel input by noise with law $P_1$. The induced Eve states are $\omega_v=\rho_E(L_vP_1)$; $\delta_N^E$ denotes full trace-norm leakage, without a factor $1/2$. Let the constant codeword types satisfy $Q_N\to P_3$ and $\operatorname{supp}Q_N\subseteq\operatorname{supp}P_3$. If the sacrifice rates $\rho_{{\rm sac},N}=N^{-1}\log L_N$ have $\liminf_N\rho_{{\rm sac},N}>I(V;E)$, then there are $A,c>0$ such that, for all sufficiently large $N$,
--
--   $$\mathbb E_F\delta_N^E\le Ae^{-cN}.$$
--
--   This secrecy implication does not assume reliability. With reliable codes chosen for Bob, every $0\le R<\Delta(P_3*P_1)-\Delta(P_1)$ is achievable with vanishing average error and leakage. For every $N$, a deterministic seed has leakage at most its seed average. Balanced fibers keep the randomized index uniform for every seed, so selecting that seed preserves Bob's index-error analysis.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 10, Theorem V.3: operational achievability and deterministic seeds

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Theorem V.3, pp.10–11: exponential expected full trace-norm secrecy requires no
reliability premise; the coding theorem separately supplies reliable private codes.
The eventual strict margin is the source's liminf sacrifice-rate condition. -/
theorem operational_achievability
    {G B E : Type*} [Group G] [Fintype G] [DecidableEq G]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (UB : ProjectiveRep G B) (UE : ProjectiveRep G E)
    (rhoB : Matrix B B ℂ) (rhoE : Matrix E E ℂ)
    (hB : QAlgorithms.IsDensityMatrix rhoB) (hE : QAlgorithms.IsDensityMatrix rhoE)
    (P1 P3 : G → ℝ) (h1 : IsLaw P1) (h3 : IsLaw P3)
    (K M L : ℕ → ℕ) (H : (N : ℕ) → BalancedHash (K N) (M N) (L N))
    (phi : (N : ℕ) → Fin (K N) → Fin N → G) (Q : ℕ → G → ℝ)
    (hQ : ∀ N, 1 ≤ N → IsLaw (Q N))
    (htype : ∀ N, 1 ≤ N → HasType (phi N) (Q N))
    (hsupp : ∀ N v, 1 ≤ N → P3 v = 0 → Q N v = 0)
    (hconv : Filter.Tendsto Q Filter.atTop (nhds P3)) :
    let WB := orbit UB rhoB
    let WE := orbit UE rhoE
    let omega := induced WE P1
    ((∃ eta : ℝ, 0 < eta ∧ ∀ᶠ N in Filter.atTop,
        holevo P3 omega + eta ≤ Real.log (L N : ℝ) / N) →
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ N in Filter.atTop,
        expectedLeakage (H N) (phi N) omega ≤ C * Real.exp (-c * N)) ∧
      (∃ seed : (N : ℕ) → Fin (H N).seeds,
        (∀ N, hashLeakage (H N) (phi N) omega (seed N) ≤
          expectedLeakage (H N) (phi N) omega) ∧
        (∀ (N : ℕ) (s : Fin (H N).seeds) (k : Fin (K N)),
          (∑ m : Fin (M N), (M N : ℝ)⁻¹ *
            (if (H N).hash s k = m then (L N : ℝ)⁻¹ else 0)) = (K N : ℝ)⁻¹) ∧
        Filter.Tendsto (fun N => hashLeakage (H N) (phi N) omega (seed N))
          Filter.atTop (nhds 0))) ∧
    (∀ R : ℝ, 0 ≤ R →
      R < delta WB WE (convolution P3 P1) - delta WB WE P1 → AchievableRate WB WE R) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
