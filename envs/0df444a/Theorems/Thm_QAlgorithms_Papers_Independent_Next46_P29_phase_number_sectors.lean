-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_phase_number_sectors
-- name    : QAlgorithms.Papers.Independent.Next46.P29.phase_number_sectors
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:21:24.191404+00:00
-- url     : https://prove2.me/theorems/c9e101e5-d444-4973-a978-bf04b13ebb59
-- title:
--   Phase-number sectors and subnormalized conditional recovery
-- statement:
--   Use the uniform phase token of cutoff $N\ge0$ and the same number rotations on token and qubit. Let $\Pi_t$ project onto total number $t$, set $\mathcal E_t(\rho)=\Pi_t(|e_N\rangle\langle e_N|\otimes\rho)\Pi_t$, and let $D_t$ map $|n,b\rangle$ to $|b\rangle$ when $n+b=t$, and to zero otherwise. The Haar encoding is $\mathcal E_N(\rho)=\sum_{t=0}^{N+1}\mathcal E_t(\rho)$. For every qubit density operator,
--
--   $$\operatorname{Tr}\mathcal E_t(\rho)=\begin{cases}\rho_{00}/(N+1)&t=0,\\\rho_{11}/(N+1)&t=N+1,\\1/(N+1)&0<t<N+1,\end{cases}$$
--
--   and
--
--   $$D_t\mathcal E_t(\rho)D_t^\dagger=\begin{cases}\rho_{00}|0\rangle\langle0|/(N+1)&t=0,\\\rho_{11}|1\rangle\langle1|/(N+1)&t=N+1,\\\rho/(N+1)&0<t<N+1.\end{cases}$$
--
--   For every joint operator $Y$, the covariant recovery equals $\sum_{t=0}^{N+1}D_tYD_t^\dagger$. Branches are subnormalized, so zero-probability events require no division.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 11, §IV.B: number sectors and conditional recovery, Eqs.(56)–(58)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)

open QAlgorithms.Papers.Independent.Information100.P63 (mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.11–12, Eqs.(56)–(58): exact subnormalized number sectors and recovered
branches. The operator expression repairs Eq.(57)'s missing outer product and
normalization using Eqs.(48),(56). No zero-probability branch is divided by its trace. -/
theorem phase_number_sectors (N : ℕ) (rho : Matrix (Fin 2) (Fin 2) ℂ)
    (hrho : IsDensityMatrix rho) :
    phaseEncoding N rho = ∑ t ∈ Finset.range (N + 2), phaseBranch N t rho ∧
    (∀ t, t ≤ N + 1 →
      (phaseBranch N t rho).trace =
        if t = 0 then rho 0 0 / (N + 1 : ℂ)
        else if t = N + 1 then rho 1 1 / (N + 1 : ℂ)
        else (N + 1 : ℂ)⁻¹) ∧
    (∀ t, t ≤ N + 1 →
      phaseDecodedBranch N t rho =
        if t = 0 then (rho 0 0 / (N + 1 : ℂ)) • Matrix.single 0 0 1
        else if t = N + 1 then (rho 1 1 / (N + 1 : ℂ)) • Matrix.single 1 1 1
        else (N + 1 : ℂ)⁻¹ • rho) ∧
    (∀ Y, phaseRecovery N Y = ∑ t ∈ Finset.range (N + 2),
      conjSuperop (numberDecoder N t) Y) := by sorry

end QAlgorithms.Papers.Independent.Next46.P29

end
